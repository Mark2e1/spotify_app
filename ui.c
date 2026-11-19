#include "ui.h"
#include "activity_log.h"
#include "lru_cache.h"
#include "stall_watch.h"
#include "auth.h"
#include "player.h"

#include <gtk/gtk.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <ctype.h>
#include <pango/pangocairo.h>
#ifdef _WIN32
#include <windows.h>
#include <gdk/gdkwin32.h>
#endif

/* ---- safe scheduling for everything that touches the window ----------------------------------
   Background threads and timers hand their results to the main loop. When the window is closed,
   GTK destroys the widgets but results already waiting (a picture that just arrived, a playlist page,
   a timer) still ran afterwards and used widgets that no longer existed:
       gtk_widget_queue_draw: assertion 'GTK_IS_WIDGET (widget)' failed
   Now every g_idle_add / g_timeout_add in this file goes through guarded_add: once the window is
   closing, waiting callbacks are dropped instead of run. (Their data is simply abandoned: the program
   is exiting. Timers are stopped.) The destroy-notify frees the small wrapper however the source ends. */
static volatile gint app_closing;

typedef struct { GSourceFunc fn; gpointer data; int slot; } GuardedCb;

static gboolean guarded_run(gpointer p) {
    GuardedCb *g = p;
    stall_pending_done(g->slot);                                    /* the main loop got to it: no longer "waiting" */
    if (g_atomic_int_get(&app_closing)) return G_SOURCE_REMOVE;     /* window is going away: touch nothing */
    return g->fn(g->data);
}

/* kind 0 = timer, 1 = idle (priority 200: after layout and painting - only for work that must wait for them),
 * 2 = HAND-OFF of a result from a worker thread (priority 0).
 * Hand-offs used to be idle sources. GLib runs a source only when nothing of lower priority number is ready,
 * and the window's painting (priority 120) and animation timers can be ready back-to-back for as long as
 * something animates, so a finished download could sit unprocessed indefinitely while the window looked alive.
 * At priority 0 a result is taken on the next loop pass and never waits for painting to pause. Every hand-off
 * is registered with stall_watch, which reports one that is not run within 3 s. */
static guint guarded_add(int kind, guint ms, GSourceFunc fn, gpointer data, const char *name) {
    GuardedCb *g = g_new(GuardedCb, 1);
    g->fn = fn;
    g->data = data;
    g->slot = kind == 0 ? -1 : stall_pending_add(name);
    GSource *s = kind == 0 ? g_timeout_source_new(ms) : g_idle_source_new();
    g_source_set_priority(s, kind == 1 ? G_PRIORITY_DEFAULT_IDLE : G_PRIORITY_DEFAULT);
    g_source_set_callback(s, guarded_run, g, g_free);
    guint id = g_source_attach(s, NULL);
    g_source_unref(s);
    return id;
}
#define g_idle_add(f, d)        guarded_add(2, 0, (GSourceFunc)(f), (d), #f)
#define g_idle_late_add(f, d)   guarded_add(1, 0, (GSourceFunc)(f), (d), #f)
#define g_timeout_add(ms, f, d) guarded_add(0, (ms), (GSourceFunc)(f), (d), #f)

/* Copies display text into a fixed buffer. A cut never leaves half of a multi-byte character (GTK warns about
 * invalid UTF-8), and invalid input is cut at its first bad byte. */
static void copy_text(char *dst, size_t cap, const char *src) {
    if (!cap) return;
    g_strlcpy(dst, src ? src : "", cap);               /* always terminated; cutting is intended here */
    const char *bad = NULL;
    if (!g_utf8_validate(dst, -1, &bad)) dst[bad - dst] = '\0';
}

/* Copies a picture address. A cut address is a different (wrong) address: if it does not fit, no picture. */
static void copy_url(char *dst, size_t cap, const char *src) {
    if (!cap) return;
    if (!src || strlen(src) >= cap) { dst[0] = '\0'; return; }
    memcpy(dst, src, strlen(src) + 1);
}

static void on_win_destroy(GtkWidget *w, gpointer unused) {
    g_atomic_int_set(&app_closing, 1);          /* first: the widgets are destroyed right after this handler */
    stall_quiet();                              /* a closing window is not a "stall" */
    gtk_main_quit();
}

/*
 * Keys:
 *   Space        play / pause
 *   Left / Right previous / next track
 *   Up / Down    choose a playlist
 *   Enter        play the chosen playlist (double-click works too)
 *   + / -        open / close the mini player
 *   [ / ]        volume down / up (5% per press)
 *   S            shuffle on / off
 *   R            repeat off / all / one song
 *   F5           reload playlists
 *   Esc or Q     quit
 *
 * Every Spotify call runs on a worker thread so the window never freezes.
 * api_lock only orders the commands (play / queue edits); reads such as polling, playlists
 * and songs run freely, so a long playlist load can no longer hold up the Next button.
 */

static GMutex api_lock;
static volatile gint sel_seq;            /* counts song picks: only the newest pick may start playing */

static struct {
    GtkWidget    *win;
    GtkWidget    *toast;          /* green pop-up message ("Added to queue") */
    guint         toast_id;
    GtkWidget    *track, *artist, *info, *device, *time, *bar, *status, *tree;
    GtkListStore *store;

    int  logged_in;
    int  poll_busy;
    int  playing, shuffle, volume;   /* volume -1 = unknown */
    int  repeat;                     /* 0 off, 1 all, 2 one song */
    gint64 volume_until;                /* a just-pressed volume is not undone by an older poll */
    gint64 play_until, shuffle_until;   /* a just-clicked play / shuffle is not undone by an older poll */
    gint64 repeat_until;             /* ignore server value until then (just changed it) */
    long prog_ms, dur_ms;
    int    seeking;      /* user is dragging the bar */
    gint64 seek_until;   /* ignore old positions from the server until then */

    GtkListStore *tracks;       /* songs of the playlist shown with T */
    GtkWidget    *list_title;
    int  view_tracks;           /* 1 = list shows songs, 0 = playlists */
    GtkListStore *devs;         /* devices shown with V: text, id, eligible, name */
    GtkWidget    *dev_btn;      /* "Play on selected device" */
    GtkWidget    *queue_btn;    /* open / close the queue */
    GtkWidget    *mini_win, *mini_img, *mini_title, *mini_artist, *mini_play;   /* floating mini player */
    GtkWidget    *mini_plus, *mini_minus;
    int           mini_state;           /* 0 closed, 1 open (or opening), 2 closing */
    int           mini_clamping;
    char          mini_img_set[256];
    cairo_surface_t *mini_surf;         /* the round album picture (72x72), painted by mini_art_draw */
    double        mini_angle;           /* degrees, 0..360: where the picture is turned to; kept while paused */
    guint         mini_tick;            /* frame-clock callback id while it spins, 0 = still */
    gint64        mini_tick_last;       /* frame time of the previous step (microseconds), 0 = none yet */
    double        mini_vel;             /* turning speed in degrees/s (carried into the glide back to the start position) */
    int           mini_home;            /* 1 = paused: gliding back to the default (upright) position */
    double        mini_bpm;             /* tempo of the playing song, 0 = not known (yet) */
    char          mini_bpm_uri[96];     /* the song mini_bpm belongs to / is being looked up for */
    int           mini_spin_off;        /* turned off by a click on the picture; kept across songs, pauses, reopening */
    int           mini_art_down;        /* left button is down on the picture and has not moved far yet */
    double        mini_art_x, mini_art_y;   /* where it went down (screen coordinates) */
    GtkWidget    *bg;           /* ambient background behind everything */
    GtkWidget    *main_box, *list_rev, *list_btn;   /* collapsible playlist list */
    GtkWidget    *pane_top, *pane_bot;     /* player (cover, info) and list: side by side when the window is wide */
    GtkWidget    *hint, *sep, *mini_label; /* extras that give way first when space is tight */
    int           lay_wide, lay_tier;      /* current layout (see apply_layout) */
    int           list_folded, hint_force;
    int           list_open;
    double        bg_cur[3][3], bg_tgt[3][3];       /* 3 glow colors: now / target */
    guint         bg_timer;
    char          bg_set[256];                      /* artwork the colors came from */
    GtkWidget    *warn;         /* picture problem notice under the carousel */
    char          bg_want[256];                     /* artwork of the song playing now */
    char          np_artist_id[64], fx_artist[64];  /* for the genre effects */
    GtkWidget    *np_box, *np_img, *np_title, *np_artist, *np_status;   /* "Now playing" card */
    char np_uri[96], np_name[256], np_artist_s[160], np_img_url[256], np_img_set[256];
    int  view_dev, dev_busy;
    GtkListStore *queue;        /* the queue shown with 6 */
    int  view_queue;            /* 1 = list shows the queue */
    int  queue_filling;         /* ignore row changes while filling */
    guint queue_timer;          /* delayed "apply new order" */
    int  tracks_busy;
    char tracks_loading[64];   /* playlist whose songs are being fetched now */
    int  tracks_show_when_ready; /* switch the list to the songs when the first page arrives */
    int  tracks_centered;      /* the playing song has been found in the carousel */
    char context_id[64];        /* playlist that is playing right now */
    char current_uri[96];       /* song that is playing right now */
    char sel_uri[96];           /* song the user just picked, until Spotify confirms it */
    gint64 sel_until;           /* ... or this time passes (monotonic us) */
    char tracks_pl[64];         /* playlist whose songs are in `tracks` */
    char sel_pl[64];            /* playlist that was selected before pressing T */

    GtkWidget    *car;          /* the song carousel at the top */
    char          preload_ctx[64];   /* playlist we already tried to preload */
    GThreadPool  *pool;         /* downloads the pictures in the background */
} ui;


static gboolean poll_once_cb(gpointer unused);
static void select_current_track(void);
static void start_tracks_load(const char *pid, int show_list);
static void strip_update(void);
static int  strip_need_icons;          /* a switch icon is waiting for its picture */

/* ---------- small helpers (main thread only) ---------- */

static void set_status(const char *msg) {
    gtk_label_set_text(GTK_LABEL(ui.status), msg ? msg : "");
}

static const char *explain(long s) {
    static char buf[64];
    if (s >= 200 && s < 300) return NULL;

    switch (s) {
    case -1:  return "Network error";
    case 401: return "Login expired - restart the app";
    case 403: return "Spotify refused (playback control needs Premium)";
    case 404: return "No active device - open Spotify and play something";
    case 429: return "Rate limited - wait a moment";
    case -2:  return "Spotify is not open on this PC - open the Spotify app here first";
    }
    snprintf(buf, sizeof buf, "Spotify error (HTTP %ld)", s);
    return buf;
}

static void mini_update(void);
static GtkWidget *make_label(const char *text, int dim);

/* Labels that only this code writes: skip the work when nothing changed. */
static void label_markup_once(GtkWidget *l, const char *m) {
    const char *old = g_object_get_data(G_OBJECT(l), "mk");
    if (old && strcmp(old, m) == 0) return;
    g_object_set_data_full(G_OBJECT(l), "mk", g_strdup(m), g_free);
    gtk_label_set_markup(GTK_LABEL(l), m);
}

static void label_text_once(GtkWidget *l, const char *t) {
    if (strcmp(gtk_label_get_text(GTK_LABEL(l)), t) != 0) gtk_label_set_text(GTK_LABEL(l), t);
}

static void update_info(void) {
    char vol[24], buf[128];

    if (ui.volume >= 0) snprintf(vol, sizeof vol, "Volume %d%%", ui.volume);
    else                snprintf(vol, sizeof vol, "Volume n/a");

    snprintf(buf, sizeof buf, "%s   |   %s   |   Shuffle %s   |   Repeat %s",
             ui.playing ? "Playing" : "Paused", vol, ui.shuffle ? "on" : "off",
             ui.repeat == 2 ? "one" : ui.repeat == 1 ? "all" : "off");
    gtk_label_set_text(GTK_LABEL(ui.info), buf);
    mini_update();
}

static void update_time(void) {
    if (ui.seeking) return;
    char buf[64];
    long p = ui.prog_ms / 1000, d = ui.dur_ms / 1000;

    snprintf(buf, sizeof buf, "%ld:%02ld / %ld:%02ld", p / 60, p % 60, d / 60, d % 60);
    gtk_label_set_text(GTK_LABEL(ui.time), buf);

    double frac = ui.dur_ms > 0 ? (double)ui.prog_ms / (double)ui.dur_ms : 0.0;
    if (frac < 0.0) frac = 0.0;
    if (frac > 1.0) frac = 1.0;
    gtk_range_set_value(GTK_RANGE(ui.bar), frac * 1000.0);
}

/* ---------- the song carousel (top of the window) ----------
 * One row of round pictures. The picture nearest the middle is the biggest;
 * the further away, the smaller and dimmer. Scroll with the mouse wheel or
 * drag; click a picture to play that song.
 */

#define CAR_H    236
#define SZ_MAX   168.0
#define SZ_MIN   52.0
#define GAP      10.0
#define BIG_NEAR 2          /* songs this close to the middle get a sharp picture */

typedef struct {
    char name[256], artist[160], uri[96];
    char img[128];          /* small (64px) picture url */
    char big[128];          /* medium (300px) picture url */
} CItem;

typedef struct {
    gint           gen;     /* which song list this download belongs to */
    int            big;
    int            keep;    /* 1 = artwork of the playing song: never dropped by a list change */
    char           url[256];
    long           http;    /* download result, for the error message */
    unsigned char *data;
    size_t         len;
    GdkPixbuf       *pb;    /* decoded (and, for big ones, scaled) in the worker thread */
    int            bad;     /* downloaded, but not a readable picture */
    gint64         t0;      /* when the worker began (activity log) */
} ThumbJob;

typedef struct { int i; double x, size, d; } Slot;

static CItem      *citems;
static int         cn;
static int         car_mini;          /* 1 = only previous / current / next */
static double      car_cx, car_target;/* position of the middle, in songs */
static guint       car_anim;          /* frame-clock callback id while the middle is moving, 0 = still */
static double      car_vel;           /* songs per second: kept when the target changes, so there is no snap */
static gint64      car_tick_last;     /* frame time of the previous step (microseconds), 0 = none yet */
/* Cover caches (lru_cache.c): url -> Cover, limited by memory first, entry count second, least recently used leave first.
 * A Cover owns the decoded picture AND the cairo surface that is painted from (never converted per frame);
 * both are counted in the budget and released together. Main thread only (workers just decode). */
typedef struct { GdkPixbuf *pb; cairo_surface_t *sf; } Cover;
static LruCache   *thumbs;            /* small pictures */
static LruCache   *bigs;              /* sharp pictures of the songs near the middle */

#define THUMB_BUDGET  ((size_t)64 << 20)
#define THUMB_ENTRIES 600
#define BIG_BUDGET    ((size_t)64 << 20)
#define BIG_ENTRIES   30
#define PL_BUDGET     ((size_t)16 << 20)
#define PL_ENTRIES    12

static void cover_free(gpointer p) {
    Cover *cv = p;
    if (cv->pb) g_object_unref(cv->pb);          /* widgets that took their own reference keep theirs */
    if (cv->sf) cairo_surface_destroy(cv->sf);
    g_free(cv);
}
static GdkPixbuf       *cover_pb(LruCache *c, const char *url) { Cover *cv = lru_find(c, url); return cv ? cv->pb : NULL; }
static cairo_surface_t *cover_sf(LruCache *c, const char *url) { Cover *cv = lru_find(c, url); return cv ? cv->sf : NULL; }
static GHashTable *pending;           /* urls being downloaded */
static GHashTable *failed;            /* url -> time (s) before which it is not asked again */
static gint        cards_gen;
static int         car_shuf;          /* 1 = shuffle order (history + queue) */
static gint        poll_reset;        /* 1 = look up previous/next songs again */

static void car_play(int i);
static void show_picture_problem(const char *msg);
static GdkPixbuf *placeholder_pixbuf(void);
static cairo_surface_t *placeholder_surface(void);
static void np_update(int changed);
static void bg_update(void);
static void fx_track(void);
static void set_list_open(int open);
static gboolean queue_reload_cb(gpointer unused);
static void car_request_big(void);

static double car_scale = 1.0;            /* smaller windows: slightly smaller (never tiny) pictures */

static double sz_at(double d) {
    return (SZ_MIN + (SZ_MAX - SZ_MIN) * exp(-0.85 * d)) * car_scale;
}

/* A picture that just failed is not requested again for 30 s (scrolling would re-ask all the time). */
static int pic_recently_failed(const char *url) {
    gpointer until = NULL;
    if (!g_hash_table_lookup_extended(failed, url, NULL, &until)) return 0;
    if (g_get_monotonic_time() / G_USEC_PER_SEC < (gint64)(gsize)until) return 1;
    g_hash_table_remove(failed, url);
    return 0;
}

/* ---- picture-pool bookkeeping (shutdown) ----
 * thumb_outstanding counts jobs pushed to ui.pool and not yet finished (queued or running). Every push goes
 * through thumb_push (main thread only); thumb_worker decrements when it is completely done with a job.
 * ui_pool_shutdown (after gtk_main) uses it to wait a bounded time instead of blocking on a curl download. */
static volatile gint thumb_outstanding;
static void thumb_push(ThumbJob *j) {
    g_atomic_int_inc(&thumb_outstanding);
    g_thread_pool_push(ui.pool, j, NULL);
}

static void car_queue(const char *url, int big) {
    if (!url[0]) return;
    LruCache *cache = big ? bigs : thumbs;
    if (g_hash_table_contains(pending, url)) return;      /* (checked first: no miss is counted while it is on its way) */
    if (pic_recently_failed(url)) return;
    if (lru_get(cache, url)) return;                      /* in memory: hit */

    g_hash_table_add(pending, g_strdup(url));

    ThumbJob *j = g_new0(ThumbJob, 1);
    j->gen = g_atomic_int_get(&cards_gen);
    j->big = big;
    snprintf(j->url, sizeof j->url, "%s", url);
    thumb_push(j);
}

/* The picture of the song that is playing: from the caches, or downloaded now.
 * These downloads are kept even when the carousel list changes, and a picture
 * that fails is not asked for again right away. */
static GdkPixbuf *art_lookup(const char *url) {
    if (!url[0]) return NULL;

    GdkPixbuf *pb = cover_pb(bigs, url);                /* borrowed: the callers use it at once (they scale / copy it) */
    if (!pb) pb = cover_pb(thumbs, url);
    if (pb) return pb;

    if (pic_recently_failed(url)) return NULL;         /* failed lately: wait before retrying */
    if (g_hash_table_contains(pending, url)) return NULL;   /* already on its way */

    g_hash_table_add(pending, g_strdup(url));
    ThumbJob *j = g_new0(ThumbJob, 1);
    j->gen = g_atomic_int_get(&cards_gen);
    j->big = 1;
    j->keep = 1;
    snprintf(j->url, sizeof j->url, "%s", url);
    thumb_push(j);
    return NULL;
}

/* Gray rounded square with a music note, for when there is no cover. */
static GdkPixbuf *placeholder_pixbuf(void) {
    static GdkPixbuf *ph;
    if (ph) return ph;

    const int S = 72;
    cairo_surface_t *sf = cairo_image_surface_create(CAIRO_FORMAT_ARGB32, S, S);
    cairo_t *cr = cairo_create(sf);
    cairo_arc(cr, S / 2.0, S / 2.0, S / 2.0, 0, 2 * G_PI);
    cairo_set_source_rgb(cr, 0.22, 0.22, 0.22);
    cairo_fill(cr);

    cairo_set_source_rgb(cr, 0.65, 0.65, 0.65);                 /* music note, no font needed */
    cairo_save(cr);
    cairo_translate(cr, 28, 49);
    cairo_rotate(cr, -0.35);
    cairo_scale(cr, 9.5, 6.5);
    cairo_arc(cr, 0, 0, 1, 0, 2 * G_PI);
    cairo_restore(cr);
    cairo_fill(cr);
    cairo_rectangle(cr, 34.5, 20, 3.2, 28);                    /* stem */
    cairo_fill(cr);
    cairo_move_to(cr, 37.7, 20);                               /* flag */
    cairo_curve_to(cr, 44, 24, 51, 28, 49, 38);
    cairo_curve_to(cr, 47, 31, 43, 30, 37.7, 29);
    cairo_close_path(cr);
    cairo_fill(cr);
    cairo_destroy(cr);

    ph = gdk_pixbuf_get_from_surface(sf, 0, 0, S, S);
    cairo_surface_destroy(sf);
    return ph;
}

static void show_picture_problem(const char *msg) {
    if (!ui.warn) return;
    gtk_label_set_text(GTK_LABEL(ui.warn), msg);
    gtk_widget_show(ui.warn);
}

/* Spotify pictures are JPEG: without the gdk-pixbuf JPEG loader every picture stays blank. */
static void check_image_support(void) {
    player_log("[build] compiled %s %s\n", __DATE__, __TIME__);   /* proves which exe is running */
    int jpeg = 0, png = 0;
    for (GSList *l = gdk_pixbuf_get_formats(); l; l = l->next) {
        char *n = gdk_pixbuf_format_get_name(l->data);
        if (n && strcmp(n, "jpeg") == 0) jpeg = 1;
        if (n && strcmp(n, "png") == 0)  png = 1;
        player_log("[icons] image format available: %s\n", n ? n : "?");
        g_free(n);
    }
    if (!jpeg)
        show_picture_problem("JPEG picture support is missing - copy the gdk-pixbuf loaders "
                             "and libjpeg DLL next to the app (see the console message)");
    player_log("[icons] jpeg loader: %s, png loader: %s\n", jpeg ? "ok" : "MISSING", png ? "ok" : "MISSING");
}

static void car_request_big(void) {
    if (cn <= 0) return;
    int c = (int)floor(car_target + 0.5);
    for (int i = c - BIG_NEAR; i <= c + BIG_NEAR; i++)
        if (i >= 0 && i < cn) car_queue(citems[i].big, 1);
}

static gint img_ok, img_fail;      /* pictures loaded / failed this run (summary in the activity log) */

/* Stores a decoded picture + its surface. 1 = the cache owns both now, 0 = refused (larger than the whole budget):
 * the caller keeps them. *evicted = how many older pictures had to leave. */
static int cover_put(LruCache *cache, const char *url, GdkPixbuf *pb, cairo_surface_t *sf, unsigned *evicted) {
    size_t px = 0, sx = 0, total = 0;
    if (!lru_mul((size_t)gdk_pixbuf_get_rowstride(pb), (size_t)gdk_pixbuf_get_height(pb), &px) ||
        !lru_mul((size_t)cairo_image_surface_get_stride(sf), (size_t)cairo_image_surface_get_height(sf), &sx) ||
        !lru_add(px, sx, &total) || !lru_add(total, sizeof(Cover), &total)) return 0;
    Cover *cv = g_new(Cover, 1);
    cv->pb = pb;
    cv->sf = sf;
    if (!lru_put(cache, url, cv, total, evicted)) { g_free(cv); return 0; }
    return 1;
}

static gboolean thumb_done(gpointer p) {
    ThumbJob *j = p;
    g_hash_table_remove(pending, j->url);
    int stored = 0;

    {   /* results of picture loading: failures always; successes counted (hundreds per playlist) */
        long ms = (long)((g_get_monotonic_time() - j->t0) / 1000);
        if (j->pb) {
            g_atomic_int_inc(&img_ok);
            if (strcmp(j->url, ui.np_img_url) == 0)
                activity_log(ACT_SUCCESS, "LOAD_IMAGE", ms, NULL, "Cover of the playing song");
        } else if (j->bad) {
            g_atomic_int_inc(&img_fail);
            activity_log(ACT_FAILED, "LOAD_IMAGE", ms, "Downloaded, but not a readable picture", "Image: %s", j->url);
        } else if (j->http != 200) {
            g_atomic_int_inc(&img_fail);
            char why[80];
            snprintf(why, sizeof why, "Download failed (HTTP %ld)", j->http);
            activity_log(ACT_FAILED, "LOAD_IMAGE", ms, why, "Image: %s", j->url);
        }
    }

    if (j->bad)                                       /* downloaded fine, but cannot be read as a picture */
        show_picture_problem("Pictures could not be decoded - the image loader files are missing "
                             "(see the console message)");

    if (j->pb) {                                      /* decoded in the worker; the paintable copy is made here, once */
        cairo_surface_t *sf = gdk_cairo_surface_create_from_pixbuf(j->pb, 1, NULL);
        if (sf && cairo_surface_status(sf) == CAIRO_STATUS_SUCCESS) {
            unsigned evicted = 0;
            if (cover_put(j->big ? bigs : thumbs, j->url, j->pb, sf, &evicted)) {
                j->pb = NULL;                         /* the cache owns both now */
                if (evicted && j->big) car_request_big();
                if (ui.car) gtk_widget_queue_draw(ui.car);
                if (strip_need_icons) strip_update();
                stored = 1;
            } else {
                player_log("[icons] picture larger than the cache budget, not cached: %s\n", j->url);
                cairo_surface_destroy(sf);
            }
        } else {
            player_log("[icons] could not prepare picture for drawing: %s\n", j->url);
            if (sf) cairo_surface_destroy(sf);
        }
    }

    if (!j->data && !j->pb && !j->bad && j->http && j->http != 200) {
        char m[160];
        snprintf(m, sizeof m, "Pictures could not be downloaded (HTTP %ld)", j->http);
        show_picture_problem(m);
    }
    if (stored && ui.warn && gtk_widget_get_visible(ui.warn))
        gtk_widget_hide(ui.warn);                     /* pictures work again */

    if (!stored)                                      /* could not get it: retry later, not at once */
        g_hash_table_replace(failed, g_strdup(j->url),
                             (gpointer)(gsize)(g_get_monotonic_time() / G_USEC_PER_SEC + 30));
    if (strcmp(j->url, ui.np_img_url) == 0) {         /* picture of the playing song arrived */
        np_update(0);
        bg_update();
        mini_update();
    }

    if (j->pb) g_object_unref(j->pb);                 /* (only if it was not stored) */
    free(j->data);
    g_free(j);
    return G_SOURCE_REMOVE;
}

/* Pictures for the songs in the middle jump the queue. */
static gint job_order(gconstpointer a, gconstpointer b, gpointer unused) {
    return ((const ThumbJob *)b)->big - ((const ThumbJob *)a)->big;
}

static void thumb_worker(gpointer data, gpointer unused) {
    ThumbJob *j = data;
    if (g_atomic_int_get(&app_closing)) {             /* shutting down: a queued job is only freed, never downloaded */
        free(j->data);
        g_free(j);
        g_atomic_int_add(&thumb_outstanding, -1);
        return;
    }
    j->t0 = g_get_monotonic_time();

    /* Always download: even if the song list changed meanwhile, the picture is cached and
     * shown as soon as that song is on screen. (Dropping stale jobs made every picture vanish
     * whenever the list was rebuilt.) The picture comes from the disk cache when it was seen
     * before. Decoding and scaling happen here, in the background thread, so the window never
     * freezes while pictures arrive. */
    j->http = player_fetch_image(j->url, &j->data, &j->len);
    if (j->http != 200) {
        player_log("[icons] download failed (HTTP %ld): %s\n", j->http, j->url);
        free(j->data);
        j->data = NULL;
        j->len = 0;
    } else if (j->data) {
        GdkPixbufLoader *ld = gdk_pixbuf_loader_new();
        GError *err = NULL;
        gboolean ok = gdk_pixbuf_loader_write(ld, j->data, j->len, &err);
        gboolean closed = gdk_pixbuf_loader_close(ld, ok ? &err : NULL);
        GdkPixbuf *pb = ok ? gdk_pixbuf_loader_get_pixbuf(ld) : NULL;
        if (pb) {
            g_object_ref(pb);
            if (j->big) {                                    /* 300 px -> 192 px, once, here */
                GdkPixbuf *sc = gdk_pixbuf_scale_simple(pb, 192, 192, GDK_INTERP_BILINEAR);
                g_object_unref(pb);
                pb = sc;
            }
            j->pb = pb;
        }
        if (!j->pb) {
            player_log("[icons] cannot decode picture: %s (bytes=%lu write=%d close=%d) %s\n",
                       err ? err->message : "no picture came out", (unsigned long)j->len,
                       ok, closed, j->url);
            player_cover_forget(j->url);                  /* a damaged saved copy must not come back */
            j->bad = 1;
        }
        if (err) g_error_free(err);
        g_object_unref(ld);
        free(j->data);
        j->data = NULL;
        j->len = 0;
    }
    if (g_atomic_int_get(&app_closing)) {             /* window already going away: no hand-off, release here */
        if (j->pb) g_object_unref(j->pb);
        free(j->data);
        g_free(j);
    } else
        g_idle_add(thumb_done, j);
    g_atomic_int_add(&thumb_outstanding, -1);    /* last: ui_pool_shutdown may free the pool once this is 0 */
}

/* Called once after gtk_main returns. app_closing is already set, so every still-queued job is freed by
 * thumb_worker without downloading, and a running one skips its hand-off. Wait for that at most ~1.5 s
 * (a running download can last up to its 15 s curl timeout; the window must not hang for it). If all
 * jobs are done, free the pool and wait for its threads (cannot block). Otherwise free it without waiting:
 * GLib keeps the pool alive until the busy threads finish and they drain the rest as above. */
static void ui_pool_shutdown(void) {
    g_atomic_int_set(&app_closing, 1);
    if (!ui.pool) return;
    gint64 until = g_get_monotonic_time() + 1500 * 1000;
    while (g_atomic_int_get(&thumb_outstanding) > 0 && g_get_monotonic_time() < until)
        g_usleep(5 * 1000);
    int idle = g_atomic_int_get(&thumb_outstanding) == 0;
    g_thread_pool_free(ui.pool, FALSE, idle ? TRUE : FALSE);
    ui.pool = NULL;
}

/* The gray "no cover" disc as a ready-to-paint surface (made once, at first use on the main thread). */
static cairo_surface_t *placeholder_surface(void) {
    static cairo_surface_t *sf;
    if (!sf) {
        GdkPixbuf *pb = placeholder_pixbuf();
        if (pb) sf = gdk_cairo_surface_create_from_pixbuf(pb, 1, NULL);
    }
    return sf;
}

/* ---- layout: size depends on the distance from the middle ---- */

static double car_cy(int H) { return (H - 44) / 2.0; }

static int car_layout(double w, Slot *out, int max) {
    if (cn <= 0) return 0;

    double cx = car_cx;
    if (cx < 0) cx = 0;
    if (cx > cn - 1) cx = cn - 1;

    int f = (int)floor(cx);
    if (f > cn - 1) f = cn - 1;
    double frac = cx - f;

    double sf = sz_at(fabs(f - cx));
    double xf = w / 2;
    if (f + 1 < cn)
        xf = w / 2 - frac * (sf / 2 + GAP + sz_at(fabs(f + 1 - cx)) / 2);

    int n = 0;
    out[n++] = (Slot){ f, xf, sf, fabs(f - cx) };

    double x = xf, s = sf;
    for (int i = f + 1; i < cn && n < max; i++) {
        double si = sz_at(fabs(i - cx));
        x += s / 2 + GAP + si / 2;
        s = si;
        if (x - si / 2 > w) break;
        out[n++] = (Slot){ i, x, si, fabs(i - cx) };
    }

    x = xf;
    s = sf;
    for (int i = f - 1; i >= 0 && n < max; i--) {
        double si = sz_at(fabs(i - cx));
        x -= s / 2 + GAP + si / 2;
        s = si;
        if (x + si / 2 < 0) break;
        out[n++] = (Slot){ i, x, si, fabs(i - cx) };
    }
    return n;
}

static int car_hit(double px, double py, int W, int H) {
    Slot sl[64];
    int n = car_layout(W, sl, 64);
    int best = -1;
    double bestv = 0;

    for (int k = 0; k < n; k++) {
        double dx = px - sl[k].x, dy = py - car_cy(H);
        double dist = sqrt(dx * dx + dy * dy);
        if (dist <= sl[k].size / 2 && (best < 0 || dist / sl[k].size < bestv)) {
            best = sl[k].i;
            bestv = dist / sl[k].size;
        }
    }
    return best;
}

static void car_text(cairo_t *cr, double W, double y, const char *txt,
                     const char *font, double r, double g, double b) {
    PangoLayout *ly = pango_cairo_create_layout(cr);
    PangoFontDescription *fd = pango_font_description_from_string(font);
    pango_layout_set_font_description(ly, fd);
    pango_font_description_free(fd);
    pango_layout_set_width(ly, (int)((W - 24) * PANGO_SCALE));
    pango_layout_set_ellipsize(ly, PANGO_ELLIPSIZE_END);
    pango_layout_set_alignment(ly, PANGO_ALIGN_CENTER);
    pango_layout_set_text(ly, txt, -1);
    cairo_set_source_rgb(cr, r, g, b);
    cairo_move_to(cr, 12, y);
    pango_cairo_show_layout(cr, ly);
    g_object_unref(ly);
}

static gboolean car_draw(GtkWidget *w, cairo_t *cr, gpointer unused) {
    int W = gtk_widget_get_allocated_width(w);
    int H = gtk_widget_get_allocated_height(w);

    if (cn <= 0) {
        car_text(cr, W, H / 2.0 - 10, "Songs appear here once a playlist is playing",
                 "Sans 11", 0.5, 0.5, 0.5);
        return TRUE;
    }

    Slot sl[64];
    int n = car_layout(W, sl, 64);
    double cy = car_cy(H);

    for (int k = 0; k < n; k++) {
        const CItem *it = &citems[sl[k].i];
        double rad = sl[k].size / 2.0;
        double alpha = 0.45 + 0.55 * exp(-0.85 * sl[k].d);

        /* painted from ready-made surfaces: converting a pixbuf on every frame was the main drawing cost */
        cairo_surface_t *sf = it->big[0] ? cover_sf(bigs, it->big) : NULL;
        if (!sf && it->img[0]) sf = cover_sf(thumbs, it->img);
        if (!sf) {
            car_queue(it->img, 0);                         /* left the cache (or never arrived): from disk / network again */
            sf = placeholder_surface();                    /* clean fallback while / if there is no cover */
        }

        cairo_save(cr);
        cairo_arc(cr, sl[k].x, cy, rad, 0, 2 * G_PI);
        cairo_clip(cr);
        if (sf) {
            double pw = cairo_image_surface_get_width(sf), ph = cairo_image_surface_get_height(sf);
            cairo_translate(cr, sl[k].x - rad, cy - rad);
            cairo_scale(cr, sl[k].size / pw, sl[k].size / ph);
            cairo_set_source_surface(cr, sf, 0, 0);
            cairo_pattern_set_filter(cairo_get_source(cr), CAIRO_FILTER_GOOD);
            cairo_paint_with_alpha(cr, alpha);
        }
        cairo_restore(cr);

        if (ui.current_uri[0] && strcmp(it->uri, ui.current_uri) == 0) {
            cairo_arc(cr, sl[k].x, cy, rad + 2, 0, 2 * G_PI);   /* playing now */
            cairo_set_source_rgb(cr, 0.114, 0.725, 0.329);
            cairo_set_line_width(cr, 3);
            cairo_stroke(cr);
        }
    }

    int mid = (int)floor(car_cx + 0.5);
    if (mid < 0) mid = 0;
    if (mid > cn - 1) mid = cn - 1;
    /* The playing song is already named by the labels below; the caption is only for a
       different song you scroll to (otherwise the title showed twice). */
    if (strcmp(citems[mid].uri, ui.current_uri) != 0) {
        car_text(cr, W, H - 42, citems[mid].name, "Sans Bold 12", 1, 1, 1);
        car_text(cr, W, H - 22, citems[mid].artist, "Sans 10", 0.7, 0.7, 0.7);
    }
    return TRUE;
}

/* ---- moving the middle ---- */

/* The middle glides to its target along an ease-in-out curve (a cubic through the start position AND the speed it
 * already has, ending at rest): it starts and stops softly, never snaps, and picking another picture while it is
 * still moving bends the motion from where it is instead of restarting it. It follows real time, so it is the same at
 * 30, 60 or 144 Hz, and is driven by the frame clock, so every step is a drawn frame. Far pictures take a little longer
 * (0.3 s for the next one, 0.9 s at most) so the trip stays readable. */
static double car_a_p0, car_a_v0, car_a_el, car_a_dur;      /* start position, start speed, time so far, length */

static gboolean car_tick(GtkWidget *w, GdkFrameClock *fc, gpointer unused) {
    gint64 now = gdk_frame_clock_get_frame_time(fc);
    double dt = car_tick_last ? (double)(now - car_tick_last) / 1e6 : 1.0 / 60.0;   /* first frame: one normal step */
    car_tick_last = now;
    if (dt > 0.05) dt = 0.05;                /* after a stall: a normal step, not a leap along the curve */
    car_a_el += dt;

    double u = car_a_el / car_a_dur;
    if (u >= 1.0) {
        car_cx = car_target;
        car_vel = 0;
        car_anim = 0;
        car_tick_last = 0;
        gtk_widget_queue_draw(w);
        return G_SOURCE_REMOVE;
    }
    double m0 = car_a_v0 * car_a_dur;        /* start speed, in "songs per whole move" */
    double dist = car_target - car_a_p0;
    double lim = 2.0 * fabs(dist) + 1.0;     /* a tiny move must not swing out because of a big old speed */
    if (m0 > lim) m0 = lim;
    if (m0 < -lim) m0 = -lim;
    double u2 = u * u, u3 = u2 * u;
    car_cx = car_a_p0 + dist * (3.0 * u2 - 2.0 * u3) + m0 * (u3 - 2.0 * u2 + u);
    car_vel = (dist * (6.0 * u - 6.0 * u2) + m0 * (3.0 * u2 - 4.0 * u + 1.0)) / car_a_dur;
    gtk_widget_queue_draw(w);
    return G_SOURCE_CONTINUE;
}

/* Ends a running glide (the tick would otherwise keep steering towards the old curve). */
static void car_stop_glide(void) {
    if (car_anim && ui.car) gtk_widget_remove_tick_callback(ui.car, car_anim);
    car_anim = 0;
    car_tick_last = 0;
}

static void car_goto(double t, int instant) {
    if (cn <= 0) { car_stop_glide(); car_cx = car_target = 0; car_vel = 0; return; }
    if (t < 0) t = 0;
    if (t > cn - 1) t = cn - 1;

    car_target = t;
    if (instant || !ui.car) {
        car_stop_glide();
        car_cx = t;
        car_vel = 0;
        if (ui.car) gtk_widget_queue_draw(ui.car);
    } else {
        double dist = fabs(t - car_cx);
        if (dist < 0.002 && fabs(car_vel) < 0.02) {
            car_cx = t;                                  /* already there */
            car_vel = 0;
        } else {
            car_a_p0 = car_cx;                           /* (re)start the curve from here, at the speed it has now */
            car_a_v0 = car_vel;
            car_a_el = 0;
            car_a_dur = 0.30 + 0.12 * log2(1.0 + dist);
            if (car_a_dur > 0.90) car_a_dur = 0.90;
            if (!car_anim) {
                car_tick_last = 0;
                car_anim = gtk_widget_add_tick_callback(ui.car, car_tick, NULL, NULL);
            }
        }
    }
    car_request_big();
}

/* The list shows the songs of the pictures (row N = picture N): keep its selected row on the picture that was chosen. */
static void list_select_card(int i) {
    GtkTreeModel *model = gtk_tree_view_get_model(GTK_TREE_VIEW(ui.tree));
    if (model != GTK_TREE_MODEL(ui.tracks) || car_mini || cn <= 0 || i < 0 || i >= cn) return;
    if (gtk_tree_model_iter_n_children(model, NULL) != cn) return;
    GtkTreeIter it;
    if (!gtk_tree_model_iter_nth_child(model, &it, NULL, i)) return;
    GtkTreeSelection *sel = gtk_tree_view_get_selection(GTK_TREE_VIEW(ui.tree));
    if (gtk_tree_selection_iter_is_selected(sel, &it)) return;
    gtk_tree_selection_select_iter(sel, &it);
    GtkTreePath *path = gtk_tree_model_get_path(model, &it);
    gtk_tree_view_scroll_to_cell(GTK_TREE_VIEW(ui.tree), path, NULL, FALSE, 0, 0);   /* only as far as needed */
    gtk_tree_path_free(path);
}

/* A picture was chosen (click, wheel, end of a drag): glide there and keep the list's selection on it. */
static void car_select(int i) {
    if (cn <= 0) return;
    if (i < 0) i = 0;
    if (i > cn - 1) i = cn - 1;
    car_goto(i, 0);
    list_select_card(i);
}

static int center_cards_on_current(int instant) {
    if (!ui.current_uri[0]) return 0;
    int best = -1;                          /* same song twice: take the copy nearest the middle */
    for (int i = 0; i < cn; i++)
        if (strcmp(citems[i].uri, ui.current_uri) == 0 &&
            (best < 0 || fabs(i - car_target) < fabs(best - car_target)))
            best = i;
    if (best < 0) return 0;
    car_goto(best, instant);
    return 1;
}

static gboolean car_scroll(GtkWidget *w, GdkEventScroll *ev, gpointer unused) {
    static double acc;
    double step = 0;

    switch (ev->direction) {
    case GDK_SCROLL_UP:
    case GDK_SCROLL_LEFT:   step = -1; break;
    case GDK_SCROLL_DOWN:
    case GDK_SCROLL_RIGHT:  step = 1; break;
    case GDK_SCROLL_SMOOTH:
        acc += (ev->delta_y != 0 ? ev->delta_y : ev->delta_x);
        if (acc >= 1 || acc <= -1) {
            step = (acc > 0) ? floor(acc) : ceil(acc);
            acc -= step;
        }
        break;
    default: break;
    }

    if (step != 0) car_select((int)floor(car_target + 0.5) + (int)step);
    return TRUE;
}

static double drag_x0, drag_cx0;
static int    pressing, dragging;

static gboolean car_press(GtkWidget *w, GdkEventButton *ev, gpointer unused) {
    if (ev->button != 1 || ev->type != GDK_BUTTON_PRESS) return FALSE;
    pressing = 1;
    dragging = 0;
    drag_x0 = ev->x;
    drag_cx0 = car_cx;
    return TRUE;
}

static gboolean car_motion(GtkWidget *w, GdkEventMotion *ev, gpointer unused) {
    if (!pressing) return FALSE;

    double dx = ev->x - drag_x0;
    if (!dragging && fabs(dx) > 6) dragging = 1;

    if (dragging && cn > 0) {
        double t = drag_cx0 - dx / 90.0;
        if (t < 0) t = 0;
        if (t > cn - 1) t = cn - 1;
        car_stop_glide();
        car_cx = car_target = t;
        car_vel = 0;                       /* the hand moves it now: nothing of an earlier glide is left */
        gtk_widget_queue_draw(w);
    }
    return TRUE;
}

static gboolean car_release(GtkWidget *w, GdkEventButton *ev, gpointer unused) {
    if (!pressing) return FALSE;
    pressing = 0;

    if (dragging) {                       /* a drag only scrolls */
        dragging = 0;
        car_select((int)floor(car_cx + 0.5));      /* settles on the nearest picture */
        return TRUE;
    }

    int i = car_hit(ev->x, ev->y, gtk_widget_get_allocated_width(w),
                    gtk_widget_get_allocated_height(w));
    if (i >= 0) car_play(i);
    return TRUE;
}

static void car_realize(GtkWidget *w, gpointer unused) {
    GdkCursor *c = gdk_cursor_new_from_name(gtk_widget_get_display(w), "pointer");
    if (c) {
        gdk_window_set_cursor(gtk_widget_get_window(w), c);
        g_object_unref(c);
    }
}

/* ---- filling the carousel ---- */

static void item_from_brief(CItem *c, const TrackBrief *b) {
    snprintf(c->name, sizeof c->name, "%s", b->name);
    copy_text(c->artist, sizeof c->artist, b->artist);
    snprintf(c->uri, sizeof c->uri, "%s", b->uri);
    copy_url(c->big, sizeof c->big, b->img);
}

/* Only previous / current / next songs (used until a whole playlist is
   loaded, and when the music is not playing from one of your playlists). */
static void car_set_mini(const TrackBrief *prev, int have_prev,
                         const PlayerState *st,
                         const TrackBrief *next, int n_next) {
    g_atomic_int_inc(&cards_gen);
    g_hash_table_remove_all(pending);

    free(citems);
    int total = (have_prev ? 1 : 0) + 1 + n_next;
    citems = calloc((size_t)total, sizeof *citems);
    cn = citems ? total : 0;
    car_mini = 1;
    car_shuf = 0;
    if (!citems) return;

    int k = 0;
    if (have_prev) item_from_brief(&citems[k++], prev);

    int cur = k++;
    snprintf(citems[cur].name, sizeof citems[cur].name, "%s", st->track);
    copy_text(citems[cur].artist, sizeof citems[cur].artist, st->artist);
    snprintf(citems[cur].uri, sizeof citems[cur].uri, "%s", st->track_uri);
    copy_url(citems[cur].big, sizeof citems[cur].big, st->img);

    for (int i = 0; i < n_next; i++) item_from_brief(&citems[k++], &next[i]);

    car_goto(cur, 1);
}

/* Shuffle on: show the songs in the order they will really play -
   what was played before, the current song, then the queue. */
static void car_set_queue(const TrackBrief *hist, int n_hist,
                          const PlayerState *st,
                          const TrackBrief *que, int n_que) {
    g_atomic_int_inc(&cards_gen);
    g_hash_table_remove_all(pending);

    free(citems);
    int total = n_hist + 1 + n_que;
    citems = calloc((size_t)total, sizeof *citems);
    cn = citems ? total : 0;
    car_mini = 1;
    car_shuf = 1;
    if (!citems) return;

    int k = 0;
    for (int i = n_hist - 1; i >= 0; i--) item_from_brief(&citems[k++], &hist[i]);

    int cur = k++;
    snprintf(citems[cur].name, sizeof citems[cur].name, "%s", st->track);
    copy_text(citems[cur].artist, sizeof citems[cur].artist, st->artist);
    snprintf(citems[cur].uri, sizeof citems[cur].uri, "%s", st->track_uri);
    copy_url(citems[cur].big, sizeof citems[cur].big, st->img);

    for (int i = 0; i < n_que; i++) item_from_brief(&citems[k++], &que[i]);

    car_goto(cur, 1);
    for (int i = 0; i < cn; i++) car_queue(citems[i].big, 1);   /* few songs: load all */
}

static void car_clear_mini(void) {
    if (!car_mini) return;
    free(citems);
    citems = NULL;
    cn = 0;
    car_mini = 0;
    car_shuf = 0;
    gtk_widget_queue_draw(ui.car);
}

/* ---------- polling the current playback state ---------- */

typedef struct {
    PlayerState st;
    long        status;
    int         extras;               /* 1 = prev / next below are fresh */
    int         have_prev, n_next;
    long        prev_status;
    TrackBrief  prev, next[2];
    int         shuf_mode, n_hist, n_que;    /* shuffle: real play order */
    TrackBrief  hist[8], que[15];
    int         partial;              /* 1 = song info only; the neighbours follow in a second result */
    int         wake_tried;           /* 1 = this poll asked Spotify to link this PC ... */
    long        wake;                 /* ... and this is what came back (see idle_hint) */
} PollResult;

/* Why nothing is playing, in words, from the last device check (player_wake_this_pc result). */
static int  idle_tried;                   /* the last device check (it only runs every 15-60 s) */
static long idle_w;

static const char *idle_hint(int tried, long w) {
    if (!tried)       return "Open Spotify on a device, then pick a playlist";
    if (w == 0)       return "Spotify is playing on another device - nothing is playing here";
    if (w >= 200 && w < 300) return "Spotify is open but idle - start a song, or pick one below";
    if (w == -2)      return "Spotify is not open on this PC - open the Spotify app, then press D";
    if (w == 401)     return "Login expired - restart the app";
    if (w == 403)     return "Spotify refused - controlling playback needs Spotify Premium";
    if (w == 429)     return "Spotify is busy (rate limited) - wait a moment";
    if (w == -1)      return "Can't reach Spotify - check your internet connection";
    return "Spotify did not answer - open the Spotify app and play something";
}

static int poll_fails, poll_wait;           /* failed-poll back-off: poll_wait = ticks skipped after errors 0, 1, 3, 7 (see poll_done) */

/* ---- adaptive polling ------------------------------------------------------------------------------------------
 * How often the playback state is asked for depends on what is going on (all intervals in ms):
 *   playing, window visible ........................ 2000  (POLL_BASE_MS, as before)
 *   paused for POLL_PAUSED_AFTER polls in a row .... 5000
 *   Spotify answers 204 (no device / nothing playing): 2000, 2000, 4000, 8000, then 15000 (cap)
 *   main window minimised/hidden (mini player not up) 10000 minimum
 *   after failed polls (error back-off, unchanged) ... 2000 * (poll_wait + 1) = 2, 4, 8, 16 s
 * The slowest applicable value wins. The idle level is reset (and a poll made at once) whenever the user acts, the
 * window is restored or gets the focus, or a poll finds a song playing. The 429 pause is separate (poll_now).
 * poll_next_interval_ms / poll_level_note are PURE (no GTK, no globals): everything else only feeds them. */
#define POLL_BASE_MS      2000
#define POLL_PAUSED_MS    5000
#define POLL_PAUSED_AFTER 15            /* consecutive "paused" answers (about 30 s) before the slow paused rate */
#define POLL_HIDDEN_MS    10000
#define POLL_204_CAP_MS   15000

typedef struct { int n204; int paused_polls; } PollLevel;   /* consecutive "nothing playing" / "paused" answers */

/* Records one finished poll. status = HTTP status (<= 0 / 4xx / 5xx errors leave the level alone: the error back-off
 * handles those); has_track = 200 with an active device and a track; playing = Spotify's is_playing. */
static void poll_level_note(PollLevel *lv, long status, int has_track, int playing) {
    if (status == 204 || (status == 200 && !has_track)) {
        if (lv->n204 < 8) lv->n204++;
        lv->paused_polls = 0;
    } else if (status == 200) {
        lv->n204 = 0;
        if (playing) lv->paused_polls = 0;
        else if (lv->paused_polls < 1000) lv->paused_polls++;
    }
}

/* Delay until the next regular poll. why (may be NULL) gets a short reason for the log. */
static int poll_next_interval_ms(const PollLevel *lv, int hidden, int err_wait, const char **why) {
    int ms = POLL_BASE_MS;
    const char *w = "playing";
    if (err_wait > 7) err_wait = 7;         /* poll_done never goes above 7; also keeps the multiplication far from overflow */
    if (lv->n204 >= 4)      { ms = POLL_204_CAP_MS; w = "nothing playing"; }
    else if (lv->n204 == 3) { ms = 8000;            w = "nothing playing"; }
    else if (lv->n204 == 2) { ms = 4000;            w = "nothing playing"; }
    if (lv->paused_polls >= POLL_PAUSED_AFTER && ms < POLL_PAUSED_MS) { ms = POLL_PAUSED_MS; w = "paused"; }
    if (hidden && ms < POLL_HIDDEN_MS) { ms = POLL_HIDDEN_MS; w = "window hidden"; }
    if (err_wait > 0 && POLL_BASE_MS * (err_wait + 1) > ms) { ms = POLL_BASE_MS * (err_wait + 1); w = "connection problems"; }
    if (why) *why = w;
    return ms;
}

static PollLevel poll_lv;               /* main thread only */
static guint     poll_timer_id;         /* the regular poll timer (re-armed whenever the wanted interval changes) */
static int       poll_cur_ms;           /* interval it is armed with (0 = not yet) */
static int       poll_win_gone;         /* main window iconified or withdrawn (set by on_win_state) */
static gboolean  poll_timer_cb(gpointer unused);
static void      poll_now(void);
static int       poll_retry_pending;    /* a 429 retry timer is waiting (main thread only) */
static gboolean  poll_retry_cb(gpointer unused);

/* Songs this app has added to the queue and that have not started playing yet: the same song is not added twice
 * (Spotify itself would happily queue it again and again). An entry goes when the song starts playing, or after
 * 10 minutes in case it was removed from the queue some other way. */
#define QADDED_MAX 32
static struct { char uri[96]; gint64 t; } qadded[QADDED_MAX];
static int n_qadded;

static int qadded_find(const char *uri) {
    gint64 now = g_get_monotonic_time();
    for (int i = 0; i < n_qadded; ) {
        if (now - qadded[i].t > 600 * G_USEC_PER_SEC) { qadded[i] = qadded[--n_qadded]; continue; }   /* expired */
        if (strcmp(qadded[i].uri, uri) == 0) return i;
        i++;
    }
    return -1;
}

static void qadded_remove(const char *uri) {
    int i = qadded_find(uri);
    if (i >= 0) qadded[i] = qadded[--n_qadded];
}

static void qadded_add(const char *uri) {
    if (qadded_find(uri) >= 0) return;
    if (n_qadded == QADDED_MAX) memmove(qadded, qadded + 1, sizeof qadded[0] * (QADDED_MAX - 1)), n_qadded--;
    snprintf(qadded[n_qadded].uri, sizeof qadded[n_qadded].uri, "%s", uri);
    qadded[n_qadded++].t = g_get_monotonic_time();
}

/* The mini player still shows the song, so only slow down when it is not up either. */
static int poll_hidden(void) {
    return poll_win_gone && !(ui.mini_win && gtk_widget_get_visible(ui.mini_win));
}

static int poll_want_ms(void) {
    return poll_next_interval_ms(&poll_lv, poll_hidden(), poll_wait, NULL);
}

/* (Re)starts the regular timer with ms; logs a change of level (not every tick). */
static void poll_arm(int ms) {
    if (g_atomic_int_get(&app_closing)) return;
    if (poll_timer_id) g_source_remove(poll_timer_id);
    if (ms != poll_cur_ms && poll_cur_ms != 0) {
        const char *why = "";
        poll_next_interval_ms(&poll_lv, poll_hidden(), poll_wait, &why);
        activity_log(poll_wait > 0 ? ACT_WARNING : ACT_SUCCESS, "POLL_INTERVAL", -1, NULL,
                     "Checking Spotify every %d ms (%s)", ms, why);
    }
    poll_cur_ms = ms;
    poll_timer_id = g_timeout_add((guint)ms, poll_timer_cb, NULL);
}

/* Re-arm when the wanted interval differs from the armed one (after a poll result or a window-state change). */
static void poll_resched(void) {
    if (!ui.logged_in) return;               /* before login poll_arm at login time sets the first timer */
    int ms = poll_want_ms();
    if (ms != poll_cur_ms) poll_arm(ms);
}

/* The user acted / the window came back / got the focus: forget the idle level, restart the timer at the fast rate. */
static void poll_level_reset(void) {
    poll_lv.n204 = 0;
    poll_lv.paused_polls = 0;
    if (ui.logged_in) poll_arm(poll_want_ms());
}

static gboolean poll_done(gpointer data) {
    PollResult *r = data;
    if (!r->partial) {
        ui.poll_busy = 0;                    /* a partial result is followed by the full one */
        if (r->status == 200 || r->status == 204) {
            if (poll_fails) activity_log(ACT_SUCCESS, "CONNECTION_RECOVERED", -1, NULL, "after %d failed polls", poll_fails);
            poll_fails = 0; poll_wait = 0;
        } else if (r->status < 0 || r->status >= 500 || r->status == 429) {
            if (poll_fails < 4) poll_fails++;
            poll_wait = (1 << poll_fails) / 2 - 1;      /* skipped timer ticks: 0, 1, 3, 7 -> interval 2, 4, 8, 16 s */
            if (poll_fails == 1) set_status("Connection problem - retrying");
        }
        poll_level_note(&poll_lv, r->status, r->status == 200 && r->st.active && r->st.track_uri[0], r->st.playing);
        poll_resched();                      /* the answer may call for a different interval */
    }

    if (ui.sel_uri[0]) {                     /* a song was just picked: ignore stale answers */
        if (g_get_monotonic_time() >= ui.sel_until ||
            (r->status == 200 && r->st.active && strcmp(r->st.track_uri, ui.sel_uri) == 0)) {
            ui.sel_uri[0] = '\0';            /* confirmed, or gave up waiting */
        } else {
            int was_partial = r->partial;
            g_free(r);
            if (!was_partial) g_timeout_add(300, poll_once_cb, NULL);
            return G_SOURCE_REMOVE;
        }
    }

    if (r->status == 200 && r->st.active && r->st.track_uri[0])
        qadded_remove(r->st.track_uri);          /* it is playing now: it may be queued again */

    if (r->status == 200 && r->st.active) {
        char *m = g_markup_printf_escaped(
            "<span size=\"large\" weight=\"bold\">%s</span>", r->st.track);
        gtk_label_set_markup(GTK_LABEL(ui.track), m);
        g_free(m);

        gtk_label_set_text(GTK_LABEL(ui.artist), r->st.artist);

        if (r->extras) {
            if (r->prev_status == 401 || r->prev_status == 403)
                set_status("Previous song needs a new login: delete spotify_token.json and restart");

            if (r->shuf_mode) {
                /* shuffle: the pictures follow the real play order */
                if (!ui.view_tracks)
                    car_set_queue(r->hist, r->n_hist, &r->st, r->que, r->n_que);
            } else {
                if (car_shuf) {              /* shuffle just went off: bring the playlist back */
                    car_shuf = 0;
                    ui.tracks_pl[0] = '\0';
                    ui.preload_ctx[0] = '\0';
                }
                if (cn == 0 || car_mini)
                    car_set_mini(&r->prev, r->have_prev, &r->st, r->next, r->n_next);
            }
        }

        {   /* things Spotify reports back, whoever caused them (this app, the Spotify app, a phone ...) */
            static char logged_uri[96];
            static int  logged_playing = -1;
            if (r->st.track_uri[0] && strcmp(logged_uri, r->st.track_uri) != 0) {
                snprintf(logged_uri, sizeof logged_uri, "%s", r->st.track_uri);
                activity_log(ACT_SUCCESS, "NOW_PLAYING", -1, NULL, "Song: %s - %s", r->st.track, r->st.artist);
            }
            if (logged_playing != r->st.playing) {
                if (logged_playing != -1)
                    activity_log(ACT_SUCCESS, r->st.playing ? "PLAYBACK_RESUMED" : "PLAYBACK_PAUSED", -1, NULL,
                                 "Reported by Spotify | Song: %s", r->st.track);
                logged_playing = r->st.playing;
            }
        }
        int song_changed = strcmp(ui.current_uri, r->st.track_uri) != 0;
        snprintf(ui.current_uri, sizeof ui.current_uri, "%s", r->st.track_uri);
        int ctx_changed = strcmp(ui.context_id, r->st.context_id) != 0;
        snprintf(ui.context_id, sizeof ui.context_id, "%s", r->st.context_id);
        if (ctx_changed) strip_update();             /* the note symbol follows the playing playlist */
        if (song_changed && ui.view_tracks &&
            strcmp(ui.tracks_pl, ui.context_id) == 0)
            select_current_track();
        if (song_changed && strcmp(ui.tracks_pl, ui.context_id) == 0 &&
            !center_cards_on_current(0) && !ui.tracks_busy &&
            !ui.view_tracks && !car_mini && !r->shuf_mode && r->extras)
            car_set_mini(&r->prev, r->have_prev, &r->st, r->next, r->n_next);  /* song not in the list: show what really plays */

        /* Keep the carousel on the playlist that is playing (preloads its
           songs and pictures; also when you start another playlist). */
        if (!ui.tracks_busy && !ui.view_tracks) {
            if (ui.context_id[0] && !r->st.shuffle &&
                strcmp(ui.context_id, ui.tracks_pl) != 0 &&
                strcmp(ui.context_id, ui.preload_ctx) != 0) {
                snprintf(ui.preload_ctx, sizeof ui.preload_ctx, "%s", ui.context_id);
                start_tracks_load(ui.context_id, 0);
            } else if (!ui.context_id[0] && !car_mini && cn > 0) {
                /* playing an album / single: back to previous-current-next */
                free(citems);
                citems = NULL;
                cn = 0;
                ui.tracks_pl[0] = '\0';
                g_atomic_int_set(&poll_reset, 1);
            }
        }

        gint64 now_us = g_get_monotonic_time();
        if (now_us >= ui.play_until) ui.playing = r->st.playing;
        if (!r->st.limited) {                /* the fallback answer does not know these: keep ours */
            if (now_us >= ui.shuffle_until) ui.shuffle = r->st.shuffle;
            if (now_us >= ui.repeat_until)  ui.repeat  = r->st.repeat;
            if (now_us >= ui.volume_until) ui.volume = r->st.volume;
        }
        if (g_get_monotonic_time() >= ui.seek_until)
            ui.prog_ms = r->st.progress_ms;
        ui.dur_ms  = r->st.duration_ms;
        update_info();
        update_time();

        {
            int changed = strcmp(ui.np_uri, r->st.track_uri) != 0;
            snprintf(ui.np_uri, sizeof ui.np_uri, "%s", r->st.track_uri);
            snprintf(ui.np_name, sizeof ui.np_name, "%s", r->st.track);
            copy_text(ui.np_artist_s, sizeof ui.np_artist_s, r->st.artist);
            snprintf(ui.np_img_url, sizeof ui.np_img_url, "%s", r->st.img);
            snprintf(ui.np_artist_id, sizeof ui.np_artist_id, "%s", r->st.artist_id);
            if (!ui.np_img_url[0]) {
                show_picture_problem("Spotify did not send an album picture for the playing song");
            }
            np_update(changed);
            bg_update();
            fx_track();
            mini_update();
        }

        if (r->st.device_type[0]) {
            char dv[200];
            snprintf(dv, sizeof dv, "On %s%s", r->st.device_type,
                     player_is_this_pc(r->st.device_name)
                         ? "" : "   (press D to play on this PC)");
            gtk_label_set_text(GTK_LABEL(ui.device), dv);
        } else {
            gtk_label_set_text(GTK_LABEL(ui.device), "");
        }
    } else if (r->status == 200 || r->status == 204) {
        ui.np_img_url[0] = '\0';
        ui.np_uri[0] = '\0';
        ui.np_name[0] = ui.np_artist_s[0] = '\0';
        mini_update();
        bg_update();
        fx_track();                          /* nothing playing: default background */
        car_clear_mini();
        gtk_label_set_markup(GTK_LABEL(ui.track),
            "<span size=\"large\" weight=\"bold\">Nothing playing</span>");
        if (r->wake_tried) { idle_tried = 1; idle_w = r->wake; }
        gtk_label_set_text(GTK_LABEL(ui.artist), idle_hint(idle_tried, idle_w));
        gtk_label_set_text(GTK_LABEL(ui.info), "");
        gtk_label_set_text(GTK_LABEL(ui.device),
                           "No device is playing   (press D to play on this PC)");
        ui.playing = 0;
        ui.prog_ms = ui.dur_ms = 0;
        update_time();
        mini_update();                                  /* nothing plays: the round picture stops turning */
    } else {
        const char *e = explain(r->status);
        if (e) set_status(e);
    }

    g_free(r);
    return G_SOURCE_REMOVE;
}

/* The queue and the history are asked for at the same time instead of one after the other. */
typedef struct { const char *uri; TrackBrief *out; int max; int *count; long status; int hist; } NeighJob;

static gpointer neigh_thread(gpointer d) {
    NeighJob *n = d;
    n->status = n->hist ? player_get_history(n->uri, n->out, n->max, n->count)
                        : player_get_previous(n->uri, n->out);
    return NULL;
}

static gpointer poll_thread(gpointer data) {
    PollResult *r = data;

    /* Only touched here; polls never overlap (poll_busy). */
    static char       last_uri[96];
    static int        last_shuf = -1;
    static TrackBrief last_cur, local_prev;

    r->status = player_get_state(&r->st);

    static int account_logged;
    if (!account_logged) { account_logged = 1; player_log_account(); }

    if (r->status == 204) {                  /* Spotify sees no playback: try to link this PC (every 15 s at most) */
        static gint64 last_wake;
        gint64 now = g_get_monotonic_time();
        static gint64 wake_gap = 15 * G_USEC_PER_SEC;
        if (now - last_wake > wake_gap) {
            last_wake = now;
            long w = player_wake_this_pc();
            r->wake_tried = 1;
            r->wake = w;
            if (w >= 200 && w < 300) {
                g_usleep(400000);
                r->status = player_get_state(&r->st);
                /* linked but still nothing playing: Spotify is idle, so ask less often */
                wake_gap = (r->status == 204) ? 60 * G_USEC_PER_SEC : 15 * G_USEC_PER_SEC;
            }
        }
    }

    if (g_atomic_int_compare_and_exchange(&poll_reset, 1, 0))
        last_uri[0] = '\0';

    if (r->status == 200 && r->st.active) {
        int uri_changed = strcmp(last_uri, r->st.track_uri) != 0;

        if (uri_changed || last_shuf != r->st.shuffle) {
            /* Show the new song at once; the neighbours (two more requests) follow. */
            PollResult *early = g_new(PollResult, 1);
            memcpy(early, r, sizeof *early);
            early->partial = 1;
            g_idle_add(poll_done, early);

            /* The song (or shuffle) changed: look up the neighbours once. */
            if (uri_changed) {
                if (last_uri[0]) local_prev = last_cur;

                memset(&last_cur, 0, sizeof last_cur);
                snprintf(last_cur.name, sizeof last_cur.name, "%s", r->st.track);
                snprintf(last_cur.artist, sizeof last_cur.artist, "%s", r->st.artist);
                snprintf(last_cur.uri, sizeof last_cur.uri, "%s", r->st.track_uri);
                snprintf(last_cur.img, sizeof last_cur.img, "%s", r->st.img);
            }

            long qs;
            if (r->st.shuffle) {
                NeighJob nj = { r->st.track_uri, r->hist, 8, &r->n_hist, 0, 1 };
                GThread *th = g_thread_new("hist", neigh_thread, &nj);
                qs = player_get_queue_n(r->que, 15, &r->n_que);
                g_thread_join(th);
                r->prev_status = nj.status;
                r->shuf_mode = 1;
            } else {
                NeighJob nj = { r->st.track_uri, &r->prev, 1, NULL, 0, 0 };
                GThread *th = g_thread_new("prev", neigh_thread, &nj);
                qs = player_get_queue(r->next, &r->n_next);
                g_thread_join(th);
                r->prev_status = nj.status;
                if (r->prev_status == 200) {
                    r->have_prev = 1;
                } else if (local_prev.uri[0]) {
                    r->prev = local_prev;      /* fallback: last song seen here */
                    r->have_prev = 1;
                }
            }

            r->extras = 1;
            if (qs == 200) {
                snprintf(last_uri, sizeof last_uri, "%s", r->st.track_uri);
                last_shuf = r->st.shuffle;
            }
        }
    } else {
        last_uri[0] = '\0';
        last_shuf = -1;
    }
    g_idle_add(poll_done, r);
    return NULL;
}

static void poll_now(void) {
    if (!ui.logged_in || ui.poll_busy) return;
    long rl = player_rate_limit_wait_ms();
    if (rl > 0) {                                      /* Spotify said wait (429): stay quiet, but come back right after */
        static gint64 logged_us;
        gint64 now = g_get_monotonic_time();
        if (now - logged_us > 10 * G_USEC_PER_SEC) {
            logged_us = now;
            activity_log(ACT_WARNING, "POLL_PAUSED", -1, "Spotify rate limit", "Updates resume in %ld ms", rl);
        }
        if (!poll_retry_pending) {                     /* one retry is enough: every timer tick used to add another */
            poll_retry_pending = 1;
            g_timeout_add((guint)rl + 100, poll_retry_cb, NULL);
        }
        return;
    }
    ui.poll_busy = 1;

    GThread *t = g_thread_new("poll", poll_thread, g_new0(PollResult, 1));
    g_thread_unref(t);
}

/* After failed polls (no network, server trouble) the regular poll slows down 2 s -> 4 s -> 8 s -> 16 s and returns to
 * normal by itself as soon as one succeeds: a dead connection is not hammered, and recovery needs nothing from you.
 * (Now expressed through poll_wait in poll_next_interval_ms; the timer is re-armed instead of skipping ticks, so a
 * hidden window or an idle Spotify does not wake the program every 2 s.) */

static gboolean poll_timer_cb(gpointer unused) {
    poll_now();                              /* does nothing while a poll is still running (poll_busy) */
    int ms = poll_want_ms();                 /* e.g. the mini player closed while the window is hidden */
    if (ms == poll_cur_ms) return G_SOURCE_CONTINUE;
    poll_timer_id = 0;                       /* this source ends now; poll_arm must not remove it again */
    poll_arm(ms);
    return G_SOURCE_REMOVE;
}

/* Every one-shot poll is requested because the user did something (or a command just finished): so it also ends the
 * idle level and restarts the regular timer from the fast rate. */
/* Retry after a 429 pause: not a user action, so the idle level is kept. */
static gboolean poll_retry_cb(gpointer unused) {
    (void)unused;
    poll_retry_pending = 0;
    poll_now();
    return G_SOURCE_REMOVE;
}

static gboolean poll_once_cb(gpointer unused) {
    poll_level_reset();
    poll_now();
    return G_SOURCE_REMOVE;
}

/* Window restored / focused: poll at once, at most once a second (focus changes can come in bursts). */
static void poll_wake(void) {
    static gint64 last_us;
    gint64 now = g_get_monotonic_time();
    poll_level_reset();
    if (now - last_us < G_USEC_PER_SEC) return;
    last_us = now;
    poll_now();
}

/* Moves the progress bar between polls so it looks smooth. */
static gboolean tick_cb(gpointer unused) {
    if (ui.logged_in && ui.playing && ui.dur_ms > 0) {
        ui.prog_ms += 500;
        if (ui.prog_ms > ui.dur_ms) ui.prog_ms = ui.dur_ms;
        update_time();
    }
    return G_SOURCE_CONTINUE;
}

/* ---------- commands (play, pause, next, ...) ---------- */

typedef struct {
    int  playlist;          /* 1 = play playlist `id`, 0 = plain http command */
    char method[8];
    char path[128];
    char id[64];
    char uri[96];
    int  track;             /* 1 = play song `uri` inside playlist `id` */
    int  single;            /* 1 = play only song `uri` */
    int  here;              /* 1 = move playback to this PC */
    int  flash;             /* 1 = briefly highlight the status line when it worked */
    int  multi;             /* > 0 = play the first `multi` songs of `uris` in order */
    char uris[25][96];
    long pos_ms;            /* where the first song of `uris` starts */
    int  repeat;            /* how many times to send a plain command */
    char okmsg[192];
    long status;
    int  selseq;            /* > 0 = a song pick; dropped if the user picked another meanwhile */
    int  fam, famseq;       /* command family (play/pause, shuffle, repeat, seek, volume): only the newest runs */
    gint64 t0;              /* when the request started (for the activity log) */
    long   ms;              /* how long Spotify took */
} Job;

/* Which commands are "the same kind"? Pressing one again while an older one is still waiting or running must not send
 * a second request: the newest wins, and an identical repeat is dropped outright. Next / previous are NOT in here:
 * three presses mean three skips. */
enum { FAM_NONE, FAM_PLAY, FAM_SHUFFLE, FAM_REPEAT, FAM_SEEK, FAM_VOLUME, FAM_N };
static volatile gint fam_seq[FAM_N];
static int  fam_open[FAM_N];                 /* jobs of the family not finished yet (main thread only) */
static char fam_last[FAM_N][128];            /* path of the newest one */

static int cmd_family(const char *path) {
    if (!strncmp(path, "/pause", 6) || !strncmp(path, "/play", 5)) return FAM_PLAY;
    if (!strncmp(path, "/shuffle", 8)) return FAM_SHUFFLE;
    if (!strncmp(path, "/repeat", 7))  return FAM_REPEAT;
    if (!strncmp(path, "/seek", 5))    return FAM_SEEK;
    if (!strncmp(path, "/volume", 7))  return FAM_VOLUME;
    return FAM_NONE;
}

/* Name of what a command does, for APPLICATION_ACTIVITY_LOG.txt. */
static const char *job_action(const Job *j) {
    if (j->here)     return "PLAY_ON_THIS_PC";
    if (j->track || j->single) return "PLAY_SONG";
    if (j->multi)    return "PLAY_SONGS";
    if (j->playlist) return "PLAY_PLAYLIST";
    if (strncmp(j->path, "/next", 5) == 0)     return "NEXT_SONG";
    if (strncmp(j->path, "/previous", 9) == 0) return "PREVIOUS_SONG";
    if (strncmp(j->path, "/pause", 6) == 0)    return "PAUSE";
    if (strncmp(j->path, "/play", 5) == 0)     return "RESUME";
    if (strncmp(j->path, "/shuffle", 8) == 0)  return "SHUFFLE";
    if (strncmp(j->path, "/repeat", 7) == 0)   return "REPEAT";
    if (strncmp(j->path, "/queue", 6) == 0)    return "QUEUE_ADD";
    if (strncmp(j->path, "/seek", 5) == 0)     return "SEEK";
    if (strncmp(j->path, "/volume", 7) == 0)   return "VOLUME";
    return "COMMAND";
}

static gboolean unflash_cb(gpointer unused) {
    gtk_style_context_remove_class(gtk_widget_get_style_context(ui.status), "ok");
    return G_SOURCE_REMOVE;
}

static void flash_status(void) {          /* subtle "it worked" highlight */
    gtk_style_context_add_class(gtk_widget_get_style_context(ui.status), "ok");
    g_timeout_add(1000, unflash_cb, NULL);
}

#define JOB_SKIPPED (-1000)    /* a newer pick / command of the same kind took over (not an HTTP or API status) */

static gboolean job_done(gpointer data) {
    Job *j = data;
    if (j->fam && fam_open[j->fam] > 0) fam_open[j->fam]--;
    if (j->status == JOB_SKIPPED) {                    /* replaced by a newer pick / command: nothing to report */
        activity_log(ACT_CANCELLED, job_action(j), -1, j->fam ? "Replaced by a newer command of the same kind" : "Replaced by a newer song pick", "%s", j->okmsg);
        g_free(j);
        return G_SOURCE_REMOVE;
    }
    const char *err = explain(j->status);

    /* the result comes from Spotify's answer, not from the key press */
    if (err) {
        char why[300];
        snprintf(why, sizeof why, "%s (HTTP %ld)", err, j->status);
        activity_log(ACT_FAILED, job_action(j), j->ms, why, "%s", j->okmsg);
    } else {
        activity_log(ACT_SUCCESS, job_action(j), j->ms, NULL, "%s", j->okmsg);
    }

    if (err && strncmp(j->path, "/queue?uri=", 11) == 0) {      /* the add failed: it may be tried again */
        char uri[96];
        size_t k = 0;
        for (const char *p = j->path + 11; *p && k + 1 < sizeof uri; p++) {
            if (p[0] == '%' && p[1] == '3' && p[2] == 'A') { uri[k++] = ':'; p += 2; }
            else uri[k++] = *p;
        }
        uri[k] = '\0';
        qadded_remove(uri);
    }

    if (err) {
        if (j->selseq && j->selseq == g_atomic_int_get(&sel_seq))
            ui.sel_uri[0] = '\0';             /* the pick failed: show what really plays */
        g_timeout_add(300, poll_once_cb, NULL);
        set_status(err);
    } else {
        set_status(j->okmsg);
        if (j->flash) flash_status();
        g_timeout_add(250, poll_once_cb, NULL);   /* Spotify needs a moment ... */
        g_timeout_add(1000, poll_once_cb, NULL);  /* ... and once more in case it was slow */
    }

    g_free(j);
    return G_SOURCE_REMOVE;
}

static gpointer job_thread(gpointer data) {
    Job *j = data;

    g_mutex_lock(&api_lock);
    j->t0 = g_get_monotonic_time();
    if (j->selseq && j->selseq != g_atomic_int_get(&sel_seq))
        j->status = JOB_SKIPPED;                     /* a newer pick is waiting: skip this one */
    else if (j->fam && j->famseq != g_atomic_int_get(&fam_seq[j->fam]))
        j->status = JOB_SKIPPED;                     /* the same kind of command was pressed again: only the newest runs */
    else if (j->here)     j->status = player_play_here();
    else if (j->track)    j->status = player_play_track_in_playlist(j->id, j->uri);
    else if (j->multi)    j->status = player_play_uris_at(j->uris, j->multi, j->pos_ms);
    else if (j->single)   j->status = player_play_uri(j->uri);
    else if (j->playlist) j->status = player_play_playlist_id(j->id);
    else {
        int n = j->repeat > 1 ? j->repeat : 1;
        for (int k = 0; k < n; k++) {
            j->status = player_http_cmd(j->method, j->path);
            if (j->status < 200 || j->status >= 300) break;
        }
    }
    g_mutex_unlock(&api_lock);
    j->ms = (long)((g_get_monotonic_time() - j->t0) / 1000);

    g_idle_add(job_done, j);
    return NULL;
}

static void start_job(Job *j) {
    GThread *t = g_thread_new("job", job_thread, j);
    g_thread_unref(t);
}

/* The user picked a song: show it at once, then start it in the background.
   Polls that were already under way (and still show the old song) are ignored until
   Spotify reports the picked song or 5 s pass, so nothing flips back. */
static void show_picked(const char *uri, const char *name,
                        const char *artist, const char *img);

static void select_song(Job *j, const char *uri, const char *name,
                        const char *artist, const char *img) {
    j->selseq = g_atomic_int_add(&sel_seq, 1) + 1;
    show_picked(uri, name, artist, img);
    start_job(j);
}

/* Shows a song as the current one at once (title, art, background, mini player). */
static void show_picked(const char *uri, const char *name,
                        const char *artist, const char *img) {
    snprintf(ui.sel_uri, sizeof ui.sel_uri, "%s", uri);
    ui.sel_until = g_get_monotonic_time() + 5 * G_USEC_PER_SEC;
    snprintf(ui.current_uri, sizeof ui.current_uri, "%s", uri);

    char *m = g_markup_printf_escaped("<span size=\"large\" weight=\"bold\">%s</span>", name);
    gtk_label_set_markup(GTK_LABEL(ui.track), m);
    g_free(m);
    if (artist && artist[0]) gtk_label_set_text(GTK_LABEL(ui.artist), artist);

    snprintf(ui.np_uri, sizeof ui.np_uri, "%s", uri);
    snprintf(ui.np_name, sizeof ui.np_name, "%s", name);
    if (artist && artist[0]) snprintf(ui.np_artist_s, sizeof ui.np_artist_s, "%s", artist);
    if (img && img[0]) snprintf(ui.np_img_url, sizeof ui.np_img_url, "%s", img);

    ui.playing = 1;
    ui.prog_ms = 0;
    ui.seek_until = 0;
    update_time();
    np_update(1);
    bg_update();
    mini_update();
    if (ui.view_tracks) select_current_track();
}

/* Next / previous: the carousel already knows the neighbours when it shows the real play
   order, so the new song appears immediately while the command is on its way. (A "previous"
   after 3 s only restarts the song, so that is not previewed.) */
static void send_cmd(const char *method, const char *path, const char *okmsg);

static void skip_song(int dir) {
    if (!ui.logged_in) return;

    if (cn > 0 && (car_mini || car_shuf) && ui.current_uri[0] &&
        !(dir < 0 && ui.prog_ms >= 3000)) {
        int cur = -1;
        for (int i = 0; i < cn; i++)
            if (strcmp(citems[i].uri, ui.current_uri) == 0) { cur = i; break; }
        int t = cur + dir;
        if (cur >= 0 && t >= 0 && t < cn) {
            const CItem *c = &citems[t];
            show_picked(c->uri, c->name, c->artist, c->big[0] ? c->big : c->img);
            ui.sel_until = g_get_monotonic_time() + 2 * G_USEC_PER_SEC;   /* short: it is a guess */
            car_goto(t, 0);
        }
    }
    if (dir > 0) send_cmd("POST", "/next", "Next track");
    else         send_cmd("POST", "/previous", "Previous track");
}

static void send_cmd(const char *method, const char *path, const char *okmsg) {
    if (!ui.logged_in) return;

    int fam = cmd_family(path);
    if (fam && fam_open[fam] > 0 && strcmp(fam_last[fam], path) == 0) {
        activity_log(ACT_CANCELLED, "DUPLICATE_COMMAND", -1, "Same command already on its way", "%s", okmsg);
        return;                                         /* identical and still pending: nothing new to send */
    }

    Job *j = g_new0(Job, 1);
    if (fam) {
        j->fam = fam;
        j->famseq = g_atomic_int_add(&fam_seq[fam], 1) + 1;
        fam_open[fam]++;
        snprintf(fam_last[fam], sizeof fam_last[fam], "%s", path);
    }
    snprintf(j->method, sizeof j->method, "%s", method);
    snprintf(j->path, sizeof j->path, "%s", path);
    snprintf(j->okmsg, sizeof j->okmsg, "%s", okmsg);
    start_job(j);
}

static void play_selected(void) {
    if (!ui.logged_in) return;

    GtkTreeSelection *sel = gtk_tree_view_get_selection(GTK_TREE_VIEW(ui.tree));
    GtkTreeIter it;
    if (!gtk_tree_selection_get_selected(sel, NULL, &it)) {
        set_status("Pick a playlist first (Up / Down)");
        return;
    }

    gchar *name = NULL, *id = NULL;
    gtk_tree_model_get(GTK_TREE_MODEL(ui.store), &it, 0, &name, 1, &id, -1);

    Job *j = g_new0(Job, 1);
    j->playlist = 1;
    snprintf(j->id, sizeof j->id, "%s", id ? id : "");
    snprintf(j->okmsg, sizeof j->okmsg, "Playing: %s", name ? name : "");
    start_job(j);

    /* Do not wait for Spotify to report the new playlist: fetch (or take from the cache) its songs now. */
    if (id && *id && !ui.view_tracks && !ui.view_queue && !ui.view_dev && !ui.shuffle &&
        strcmp(id, ui.tracks_pl) != 0 &&
        !(ui.tracks_busy && strcmp(id, ui.tracks_loading) == 0)) {
        snprintf(ui.preload_ctx, sizeof ui.preload_ctx, "%s", id);
        start_tracks_load(id, 0);
    }

    g_free(name);
    g_free(id);
}

static void toggle_shuffle(void) {
    if (!ui.logged_in) return;
    ui.shuffle = !ui.shuffle;
    ui.shuffle_until = g_get_monotonic_time() + 3 * G_USEC_PER_SEC;
    update_info();

    send_cmd("PUT", ui.shuffle ? "/shuffle?state=true" : "/shuffle?state=false",
             ui.shuffle ? "Shuffle on" : "Shuffle off");
}

/* R: repeat off -> all -> one song -> off */
static void toggle_repeat(void) {
    if (!ui.logged_in) return;
    ui.repeat = (ui.repeat + 1) % 3;
    ui.repeat_until = g_get_monotonic_time() + 3 * G_USEC_PER_SEC;
    update_info();
    send_cmd("PUT", ui.repeat == 2 ? "/repeat?state=track"
                  : ui.repeat == 1 ? "/repeat?state=context" : "/repeat?state=off",
             ui.repeat == 2 ? "Repeat one song" : ui.repeat == 1 ? "Repeat all" : "Repeat off");
}

/* [ and ]: volume in 5% steps. The number shows at once and is not undone by an older poll; quick presses add up
 * locally and only the newest value is sent (see the command families). */
static void change_volume(int delta) {
    if (!ui.logged_in) return;
    if (ui.volume < 0) { set_status("This device has no volume control"); return; }
    int v = ui.volume + delta;
    if (v < 0) v = 0;
    if (v > 100) v = 100;
    if (v == ui.volume) return;
    ui.volume = v;
    ui.volume_until = g_get_monotonic_time() + 3 * G_USEC_PER_SEC;
    update_info();
    char path[64], msg[48];
    snprintf(path, sizeof path, "/volume?volume_percent=%d", v);
    snprintf(msg, sizeof msg, "Volume %d%%", v);
    send_cmd("PUT", path, msg);
}

static void toggle_play(void) {
    if (!ui.logged_in) return;
    ui.play_until = g_get_monotonic_time() + 3 * G_USEC_PER_SEC;
    if (ui.playing) {
        ui.playing = 0;
        update_info();
        send_cmd("PUT", "/pause", "Paused");
    } else {
        ui.playing = 1;
        update_info();
        send_cmd("PUT", "/play", "Playing");
    }
}

/* ---------- playlists ---------- */

typedef struct {
    PlaylistInfo *items;
    int           n;
    long          status;
    gint64        t0;
} PlResult;

static gboolean playlists_done(gpointer data) {
    PlResult *r = data;

    if (r->status != 200) {
        const char *e = explain(r->status);
        set_status(e ? e : "Could not load playlists");
        char why[300];
        snprintf(why, sizeof why, "%s (HTTP %ld)", e ? e : "failed", r->status);
        activity_log(ACT_FAILED, "LOAD_PLAYLISTS", (long)((g_get_monotonic_time() - r->t0) / 1000), why, "Your playlists");
    } else {
        activity_log(r->n > 0 ? ACT_SUCCESS : ACT_WARNING, "LOAD_PLAYLISTS",
                     (long)((g_get_monotonic_time() - r->t0) / 1000), r->n > 0 ? NULL : "No playlists returned",
                     "%d playlist%s", r->n, r->n == 1 ? "" : "s");
        gtk_list_store_clear(ui.store);

        for (int i = 0; i < r->n; i++) {
            GtkTreeIter it;
            gtk_list_store_append(ui.store, &it);
            gtk_list_store_set(ui.store, &it, 0, r->items[i].name,
                               1, r->items[i].id, -1);
        }

        /* The tree view has no filter/sort wrapper, but it swaps its model between store, tracks, queue and devs.
         * Only touch the selection when the view really displays ui.store, otherwise this iter belongs to a
         * model the view is not showing (F5 while Queue / Devices is open). */
        if (r->n > 0 && !ui.view_tracks &&
            gtk_tree_view_get_model(GTK_TREE_VIEW(ui.tree)) == GTK_TREE_MODEL(ui.store)) {
            GtkTreeIter first;
            if (gtk_tree_model_get_iter_first(GTK_TREE_MODEL(ui.store), &first))
                gtk_tree_selection_select_iter(
                    gtk_tree_view_get_selection(GTK_TREE_VIEW(ui.tree)), &first);
        }

        char buf[64];
        snprintf(buf, sizeof buf, "Loaded %d playlist%s", r->n, r->n == 1 ? "" : "s");
        set_status(buf);
    }

    free(r->items);
    g_free(r);
    return G_SOURCE_REMOVE;
}

static gpointer playlists_thread(gpointer data) {
    PlResult *r = data;
    r->t0 = g_get_monotonic_time();
    r->status = player_fetch_playlists(&r->items, &r->n);
    g_idle_add(playlists_done, r);
    return NULL;
}

static void load_playlists(void) {
    if (!ui.logged_in) return;
    set_status("Loading playlists...");

    GThread *t = g_thread_new("playlists", playlists_thread, g_new0(PlResult, 1));
    g_thread_unref(t);
}

/* The picture carousel follows the song picked in the list: the picked song's picture glides to the middle (the
 * same easing as every other carousel move, so far songs are reached in well under a second) and stays
 * where it is until something else is picked. Only when the list shows the songs of the playlist the pictures show
 * (rows and pictures are appended together, so row N is picture N); never for playlists, queue or devices. */
static void follow_selected_song(void) {
    GtkTreeModel *model = gtk_tree_view_get_model(GTK_TREE_VIEW(ui.tree));
    if (model != GTK_TREE_MODEL(ui.tracks) || car_mini || cn <= 0) return;
    if (gtk_tree_model_iter_n_children(model, NULL) != cn) return;        /* still filling: the two do not match yet */

    GtkTreeIter it;
    if (!gtk_tree_selection_get_selected(gtk_tree_view_get_selection(GTK_TREE_VIEW(ui.tree)), NULL, &it)) return;
    GtkTreePath *path = gtk_tree_model_get_path(model, &it);
    int idx = path && gtk_tree_path_get_depth(path) > 0 ? gtk_tree_path_get_indices(path)[0] : -1;
    if (path) gtk_tree_path_free(path);
    if (idx < 0 || idx >= cn) return;
    if (idx == (int)floor(car_target + 0.5)) return;                     /* already in the middle: do not touch it */
    car_goto(idx, 0);                                                     /* smooth, from wherever it is now */
}

/* mouse click, Page Up / Down, Home / End: the list moved its cursor */
static void on_tree_cursor_changed(GtkTreeView *tv, gpointer unused) {
    (void)tv; (void)unused;
    follow_selected_song();
}

static void move_selection(int delta) {
    GtkTreeSelection *sel = gtk_tree_view_get_selection(GTK_TREE_VIEW(ui.tree));
    GtkTreeModel *model = gtk_tree_view_get_model(GTK_TREE_VIEW(ui.tree));
    GtkTreeIter it;

    if (!gtk_tree_selection_get_selected(sel, NULL, &it)) {
        if (!gtk_tree_model_get_iter_first(model, &it)) return;
    } else if (delta > 0) {
        if (!gtk_tree_model_iter_next(model, &it)) return;
    } else {
        if (!gtk_tree_model_iter_previous(model, &it)) return;
    }

    gtk_tree_selection_select_iter(sel, &it);

    GtkTreePath *path = gtk_tree_model_get_path(model, &it);
    gtk_tree_view_scroll_to_cell(GTK_TREE_VIEW(ui.tree), path, NULL, FALSE, 0, 0);
    gtk_tree_path_free(path);
    follow_selected_song();                                               /* Up / Down: the pictures follow */
}

/* ---------- songs of the playing playlist (T key) ---------- */

static void select_row_by_id(GtkListStore *store, const char *id, gboolean center) {
    GtkTreeModel *model = GTK_TREE_MODEL(store);
    GtkTreeIter it;

    if (!id || !id[0] || !gtk_tree_model_get_iter_first(model, &it)) return;
    /* the iter is only valid for the view if the view displays this very store (queue / devices may be open) */
    if (gtk_tree_view_get_model(GTK_TREE_VIEW(ui.tree)) != model) return;

    do {
        gchar *rid = NULL;
        gtk_tree_model_get(model, &it, 1, &rid, -1);
        int match = rid && strcmp(rid, id) == 0;
        g_free(rid);

        if (match) {
            gtk_tree_selection_select_iter(
                gtk_tree_view_get_selection(GTK_TREE_VIEW(ui.tree)), &it);

            GtkTreePath *path = gtk_tree_model_get_path(model, &it);
            gtk_tree_view_scroll_to_cell(GTK_TREE_VIEW(ui.tree), path, NULL,
                                         center, 0.5f, 0.0f);
            gtk_tree_path_free(path);
            return;
        }
    } while (gtk_tree_model_iter_next(model, &it));
}

static void select_current_track(void) {
    select_row_by_id(ui.tracks, ui.current_uri, TRUE);
}

static void remember_playlist_selection(void) {
    GtkTreeSelection *sel = gtk_tree_view_get_selection(GTK_TREE_VIEW(ui.tree));
    GtkTreeIter it;

    if (gtk_tree_selection_get_selected(sel, NULL, &it)) {
        gchar *id = NULL;
        gtk_tree_model_get(GTK_TREE_MODEL(ui.store), &it, 1, &id, -1);
        snprintf(ui.sel_pl, sizeof ui.sel_pl, "%s", id ? id : "");
        g_free(id);
    }
}

typedef struct {
    TrackInfo *items;
    int        n;
    long       status;
    char       playlist_id[64];
    int        show_list;     /* 1 = also switch the list to the songs (T key) */
    int        req;           /* which request this belongs to (older ones are ignored) */
    int        offset;        /* page results: index of the first song */
    int        pages;         /* pages already shown */
    int        attempt;       /* retry counter */
    char       name[256];     /* playlist name, read on the main thread (the worker must not touch the GTK list) */
    int        borrowed;      /* items belong to the cache: show them, do not free them */
    gint64     t0;            /* when the download started (activity log) */
} TrkResult;

/* Songs of playlists already loaded: opening one again is instant. */
typedef struct {
    TrackInfo *items;
    int        n;
    gint64     at;            /* monotonic seconds when loaded */
    int        stale;         /* known to be out of date (Liked Songs changed): not used, read again */
} PlCache;

#define PLCACHE_FRESH 300     /* seconds a cached playlist is trusted */

static LruCache   *plcache;           /* playlist id -> PlCache; memory budget + entry limit, least recently used leave first */
static gint        tracks_req;    /* id of the newest songs request: older answers are dropped */

static void plcache_free(gpointer p) { PlCache *c = p; free(c->items); g_free(c); }
static int  in_pair(const char *id);

/* Never evicted: the two playlists of the T/P switch and the one being shown or loaded (a pending result may
 * be reading its song list without a copy). */
static int plcache_pin(const char *id, void *val, void *user) {
    (void)val; (void)user;
    return in_pair(id) || strcmp(id, ui.tracks_pl) == 0 || strcmp(id, ui.tracks_loading) == 0;
}

static void plcache_clear(void) {         /* F5: forget loaded playlists so they are read again */
    if (plcache) lru_clear(plcache);
}

/* Main-loop heartbeat for stall_watch: proves the window is alive; every 2 s also records the cache sizes. */
static gboolean beat_cb(gpointer unused) {
    static int tick;
    stall_beat();
    if (tick++ % 8 == 0 && thumbs && bigs && plcache) {
        char *a = lru_stats_text(thumbs), *b = lru_stats_text(bigs), *p = lru_stats_text(plcache);
        char *all = g_strdup_printf("%s ; %s ; %s", a, b, p);
        stall_snapshot(all);
        g_free(a); g_free(b); g_free(p); g_free(all);
    }
    return G_SOURCE_CONTINUE;
}

/* One activity-log line per cache (debugging): memory used / budget, entries, hits, evictions. */
static void cache_stats_log(const char *action) {
    LruCache *all[3] = { thumbs, bigs, plcache };
    for (int i = 0; i < 3; i++) {
        if (!all[i]) continue;
        char *t = lru_stats_text(all[i]);
        activity_log(ACT_SUCCESS, action, -1, NULL, "%s", t);
        g_free(t);
    }
}

static void show_tracks_view(const char *playlist_id) {
    char title[320] = "Songs   (T = back)";
    GtkTreeModel *pm = GTK_TREE_MODEL(ui.store);
    GtkTreeIter pit;
    if (gtk_tree_model_get_iter_first(pm, &pit)) {
        do {
            gchar *pid = NULL, *pname = NULL;
            gtk_tree_model_get(pm, &pit, 0, &pname, 1, &pid, -1);
            if (pid && pname && strcmp(pid, playlist_id) == 0)
                snprintf(title, sizeof title, "Songs in: %s   (T = back)", pname);
            g_free(pid);
            g_free(pname);
        } while (gtk_tree_model_iter_next(pm, &pit));
    }

    ui.view_tracks = 1;
    gtk_tree_view_set_model(GTK_TREE_VIEW(ui.tree), GTK_TREE_MODEL(ui.tracks));
    gtk_label_set_text(GTK_LABEL(ui.list_title), title);
    select_current_track();
    set_status("Showing songs - press T to go back");
}

/* ---- progressive songs loading ----
   The first 100 songs appear as soon as they arrive, the rest follow page by page while you
   already browse. Every request has an id; answers of an older request are thrown away, so a
   slow playlist can never overwrite the one selected later. Finished playlists are cached. */

static void cards_reset(void) {
    g_atomic_int_inc(&cards_gen);
    free(citems);                             /* (pending downloads stay: they fill the cache) */
    citems = NULL;
    cn = 0;
    car_mini = 0;
    car_shuf = 0;
}

/* ---- two-playlist switch (under the pictures) ----
   Four things are kept apart:
     playing   ui.context_id         the playlist Spotify is playing (never changed by the switch)
     viewed    ui.tracks_pl          the playlist whose songs the pictures / list show
     pair      pls.id[0], pls.id[1]  the two playlists the switch toggles between (viewed + the one before)
     loading   ui.tracks_loading     a playlist being fetched; pls.want = the one the user asked for
   Opening one that is cached shows it at once, with the carousel position and selected song it had. */
static struct {
    GtkWidget *box, *btn[2], *img[2], *now[2], *lbl[2];
    char       id[2][64];
    char       want[64];                 /* picked by the user, not shown yet */
} pls;

typedef struct { double pos; char sel[96]; char playing[96]; double scroll; } PlView;
static GHashTable *plviews;              /* playlist id -> PlView: where you were in each playlist */
static int         view_restore_force;   /* 1 while a cached playlist is shown from the switch */

static int in_pair(const char *id) {
    return id[0] && (strcmp(id, pls.id[0]) == 0 || strcmp(id, pls.id[1]) == 0);
}

static void playlist_name(const char *id, char *out, size_t sz) {
    snprintf(out, sz, "Playlist");
    GtkTreeModel *pm = GTK_TREE_MODEL(ui.store);
    GtkTreeIter it;
    if (!gtk_tree_model_get_iter_first(pm, &it)) return;
    do {
        gchar *pid = NULL, *pname = NULL;
        gtk_tree_model_get(pm, &it, 0, &pname, 1, &pid, -1);
        if (pid && pname && strcmp(pid, id) == 0) snprintf(out, sz, "%s", pname);
        g_free(pid);
        g_free(pname);
    } while (gtk_tree_model_iter_next(pm, &it));
}

/* Remember where you are in the playlist that is about to be replaced. */
static void view_save(const char *pid) {
    if (!pid[0] || cn <= 0 || car_mini) return;
    if (!plviews) plviews = g_hash_table_new_full(g_str_hash, g_str_equal, g_free, g_free);
    PlView *v = g_hash_table_lookup(plviews, pid);
    if (!v) { v = g_new0(PlView, 1); g_hash_table_insert(plviews, g_strdup(pid), v); }
    v->pos = car_target;
    snprintf(v->playing, sizeof v->playing, "%s", ui.current_uri);
    /* (the queue / devices views leave view_tracks set but put another model in the tree: only read ui.tracks rows) */
    if (ui.view_tracks && !ui.view_queue && !ui.view_dev) {
        GtkTreeSelection *sel = gtk_tree_view_get_selection(GTK_TREE_VIEW(ui.tree));
        GtkTreeIter it;
        v->sel[0] = '\0';
        if (gtk_tree_selection_get_selected(sel, NULL, &it)) {
            gchar *uri = NULL;
            gtk_tree_model_get(GTK_TREE_MODEL(ui.tracks), &it, 1, &uri, -1);
            snprintf(v->sel, sizeof v->sel, "%s", uri ? uri : "");
            g_free(uri);
        }
        GtkAdjustment *adj = gtk_scrollable_get_vadjustment(GTK_SCROLLABLE(ui.tree));
        v->scroll = adj ? gtk_adjustment_get_value(adj) : 0;
    }
}

static gboolean view_scroll_cb(gpointer data) {
    double *val = data;
    GtkAdjustment *adj = gtk_scrollable_get_vadjustment(GTK_SCROLLABLE(ui.tree));
    if (adj && ui.view_tracks) gtk_adjustment_set_value(adj, *val);
    g_free(val);
    return G_SOURCE_REMOVE;
}

/* Put the carousel, the selected song and the scroll position back. Returns 1 if there was something. */
static int view_restore(const char *pid) {
    PlView *v = plviews ? g_hash_table_lookup(plviews, pid) : NULL;
    if (!v || cn <= 0) return 0;
    /* the playing playlist follows the song that plays now, unless it is still the same song */
    if (strcmp(pid, ui.context_id) == 0 && strcmp(v->playing, ui.current_uri) != 0) return 0;
    car_goto(v->pos, 1);
    if (ui.view_tracks) {
        if (v->sel[0]) select_row_by_id(ui.tracks, v->sel, TRUE);
        double *s = g_new(double, 1);
        *s = v->scroll;
        g_idle_late_add(view_scroll_cb, s);     /* after the rows have been laid out (needs the later priority) */
    }
    return 1;
}

static void strip_update(void) {
    if (!pls.box) return;
    int show = pls.id[0][0] && pls.id[1][0] && strcmp(pls.id[0], pls.id[1]) != 0;
    int need = 0;
    for (int i = 0; i < 2; i++) {
        if (!pls.id[i][0]) continue;
        char name[256];
        playlist_name(pls.id[i], name, sizeof name);
        gtk_label_set_text(GTK_LABEL(pls.lbl[i]), name);
        gtk_widget_set_tooltip_text(pls.btn[i], name);

        int loading = ui.tracks_busy && strcmp(pls.id[i], ui.tracks_loading) == 0;
        GtkStyleContext *sc = gtk_widget_get_style_context(pls.btn[i]);
        if (strcmp(pls.id[i], ui.tracks_pl) == 0) gtk_style_context_add_class(sc, "pl-active");
        else                                      gtk_style_context_remove_class(sc, "pl-active");
        if (loading) gtk_style_context_add_class(sc, "pl-loading");
        else         gtk_style_context_remove_class(sc, "pl-loading");
        gtk_widget_set_visible(pls.now[i], ui.context_id[0] && strcmp(pls.id[i], ui.context_id) == 0);

        PlCache *c = plcache ? lru_find(plcache, pls.id[i]) : NULL;   /* icon: first cover */
        const char *url = (c && c->n > 0) ? c->items[0].img : "";
        GdkPixbuf *pb = url[0] ? cover_pb(thumbs, url) : NULL;
        if (pb) {
            GdkPixbuf *sm = gdk_pixbuf_scale_simple(pb, 24, 24, GDK_INTERP_BILINEAR);
            if (sm) { gtk_image_set_from_pixbuf(GTK_IMAGE(pls.img[i]), sm); g_object_unref(sm); }
            gtk_widget_show(pls.img[i]);
        } else {
            if (url[0]) { car_queue(url, 0); need = 1; }      /* picture still on its way: draw it when it lands */
            gtk_widget_hide(pls.img[i]);
        }
    }
    strip_need_icons = need;
    gtk_widget_set_visible(pls.box, show);
}

/* A playlist was opened with T: remember it together with the one we came from. */
static void strip_note_opened(const char *shown, const char *prev) {
    if (!in_pair(shown)) {
        const char *other = (ui.context_id[0] && strcmp(ui.context_id, shown) != 0) ? ui.context_id
                          : (prev[0] && strcmp(prev, shown) != 0) ? prev : "";
        if (other[0]) {
            snprintf(pls.id[0], sizeof pls.id[0], "%s", other);
            snprintf(pls.id[1], sizeof pls.id[1], "%s", shown);
        }
    }
    if (strcmp(pls.want, shown) == 0) pls.want[0] = '\0';
    strip_update();
}

static void strip_pick(int i) {
    if (!ui.logged_in || !pls.id[i][0]) return;
    const char *pid = pls.id[i];

    if (strcmp(pid, ui.tracks_pl) == 0 && cn > 0 && !car_mini) {      /* already showing it ... */
        if (ui.tracks_busy && strcmp(pid, ui.tracks_loading) != 0) {   /* ... so drop the other one still loading */
            g_atomic_int_inc(&tracks_req);
            ui.tracks_busy = 0;
            ui.tracks_loading[0] = '\0';
            stall_load_end();                                          /* nothing is loading any more */
        }
        pls.want[0] = '\0';
        strip_update();
        return;
    }
    if (ui.tracks_busy && strcmp(pid, ui.tracks_loading) == 0) return;  /* already on its way */

    char name[256], msg[300];
    playlist_name(pid, name, sizeof name);
    snprintf(pls.want, sizeof pls.want, "%s", pid);
    snprintf(ui.sel_pl, sizeof ui.sel_pl, "%s", pid);
    snprintf(ui.preload_ctx, sizeof ui.preload_ctx, "%s", ui.context_id);  /* the playing playlist must not pull the view back */
    snprintf(msg, sizeof msg, "Showing: %s", name);
    set_status(msg);

    view_restore_force = 1;                    /* a cached playlist is shown as it is, however old */
    start_tracks_load(pid, ui.view_tracks);
    view_restore_force = 0;
    strip_update();
}

static void strip_clicked(GtkButton *b, gpointer data) {
    (void)b;
    strip_pick(GPOINTER_TO_INT(data));
}

static void strip_swap(void) {                  /* P: to the other one of the two */
    if (!pls.box || !gtk_widget_get_visible(pls.box)) { set_status("Press T on another playlist first"); return; }
    const char *cur = pls.want[0] ? pls.want : ui.tracks_pl;    /* the last one asked for, even if still loading */
    strip_pick(strcmp(pls.id[0], cur) == 0 ? 1 : 0);
}

/* ---- search in the playlist that is shown ( / or Ctrl+F ) ----
   Typing jumps the pictures (and the song row) to the first song whose title or artist contains the
   text; Enter goes to the next match; Esc closes the box. Nothing is played until you press Enter on
   the song / click its picture, so a typo never starts music. */
static GtkWidget *search_entry;

static int search_find(const char *needle, int from) {            /* index of the next match, or -1 */
    if (cn <= 0 || !needle[0]) return -1;
    char *nd = g_utf8_strdown(needle, -1);
    int found = -1;
    for (int k = 0; k < cn && found < 0; k++) {
        int i = (from + k) % cn;
        char hay[480];
        snprintf(hay, sizeof hay, "%s %s", citems[i].name, citems[i].artist);
        char *h = g_utf8_strdown(hay, -1);
        if (strstr(h, nd)) found = i;
        g_free(h);
    }
    g_free(nd);
    return found;
}

static char search_last_q[160];            /* what the last search found, for the activity log */
static char search_last_hit[256];

static void search_go(int from) {
    const char *q = gtk_entry_get_text(GTK_ENTRY(search_entry));
    if (!q[0]) return;
    snprintf(search_last_q, sizeof search_last_q, "%s", q);
    search_last_hit[0] = '\0';
    if (cn <= 0 || car_mini) { set_status("Open a playlist first (press T)"); return; }
    int i = search_find(q, from);
    if (i < 0) { set_status("No song matches"); return; }
    snprintf(search_last_hit, sizeof search_last_hit, "%s", citems[i].name);
    car_goto(i, 0);
    if (ui.view_tracks) select_row_by_id(ui.tracks, citems[i].uri, TRUE);
    char msg[320];
    snprintf(msg, sizeof msg, "Found: %s", citems[i].name);
    set_status(msg);
}

static void search_changed(GtkSearchEntry *e, gpointer unused) {
    (void)e; (void)unused;
    search_go(0);                                  /* first match from the top as you type */
}

static void search_activate(GtkEntry *e, gpointer unused) {
    (void)e; (void)unused;
    search_go((int)floor(car_target + 0.5) + 1);   /* Enter: the next match after the one shown */
}

static void search_close(void) {
    if (!search_entry || !gtk_widget_get_visible(search_entry)) return;
    if (search_last_q[0]) {                        /* one entry per search, not one per typed letter */
        if (search_last_hit[0])
            activity_log(ACT_SUCCESS, "SEARCH_SONGS", -1, NULL, "Query: \"%s\" | Found: %s", search_last_q, search_last_hit);
        else
            activity_log(ACT_WARNING, "SEARCH_SONGS", -1, cn <= 0 ? "No playlist is open" : "No song matches",
                         "Query: \"%s\"", search_last_q);
        search_last_q[0] = '\0';
    }
    gtk_entry_set_text(GTK_ENTRY(search_entry), "");
    gtk_widget_hide(search_entry);
    gtk_widget_grab_focus(ui.tree);                /* keys work as usual again */
}

static void search_stop(GtkSearchEntry *e, gpointer unused) {
    (void)e; (void)unused;
    search_close();
}

static void search_open(void) {
    if (!ui.logged_in || !search_entry) return;
    activity_log(ACT_SUCCESS, "OPEN_PANEL", -1, NULL, "Panel: Song search");
    gtk_widget_show(search_entry);
    gtk_widget_grab_focus(search_entry);
}

static void tracks_append(const TrackInfo *items, int n) {
    CItem *grown = realloc(citems, (size_t)(cn + n) * sizeof *citems);
    int keep = grown != NULL;
    if (keep) citems = grown;

    for (int i = 0; i < n; i++) {
        const TrackInfo *t = &items[i];

        char label[600];
        if (t->artist[0]) snprintf(label, sizeof label, "%s  -  %s", t->name, t->artist);
        else              snprintf(label, sizeof label, "%s", t->name);
        GtkTreeIter it;
        gtk_list_store_append(ui.tracks, &it);
        gtk_list_store_set(ui.tracks, &it, 0, label, 1, t->uri, -1);

        if (keep) {
            CItem *c = &citems[cn + i];
            memset(c, 0, sizeof *c);
            snprintf(c->name, sizeof c->name, "%s", t->name);
            snprintf(c->artist, sizeof c->artist, "%s", t->artist);
            snprintf(c->uri, sizeof c->uri, "%s", t->uri);
            snprintf(c->img, sizeof c->img, "%s", t->img);
            snprintf(c->big, sizeof c->big, "%s", t->big);
            car_queue(t->img, 0);              /* small picture: cached or downloaded in the background */
        }
    }
    if (keep) cn += n;
}

/* One page (main thread). */
static gboolean tracks_page(gpointer data) {
    TrkResult *r = data;

    if (r->req == g_atomic_int_get(&tracks_req)) {
        if (r->offset == 0) {                  /* first page: switch over at once */
            char prev_pl[64];
            snprintf(prev_pl, sizeof prev_pl, "%s", ui.tracks_pl);
            /* view_save needs cn, car_target, car_mini, the row selection and the scroll position, which
             * gtk_list_store_clear / cards_reset wipe: it must run BEFORE them (it used to run after = dead code). */
            if (strcmp(prev_pl, r->playlist_id) != 0) view_save(prev_pl);
            gtk_list_store_clear(ui.tracks);
            cards_reset();
            snprintf(ui.tracks_pl, sizeof ui.tracks_pl, "%s", r->playlist_id);
            ui.tracks_centered = 0;
            int opened = r->show_list || ui.tracks_show_when_ready;
            if (opened) show_tracks_view(r->playlist_id);
            ui.tracks_show_when_ready = 0;
            if (strcmp(prev_pl, r->playlist_id) != 0) {
                char nm[256];
                playlist_name(r->playlist_id, nm, sizeof nm);
                activity_log(ACT_SUCCESS, "SWITCH_PLAYLIST", -1, NULL, "Playlist: %s | %s | %s", nm,
                             opened ? "opened by the user" : "followed the playing playlist",
                             r->borrowed ? "from memory" : "from Spotify");
            }
            if (opened) strip_note_opened(r->playlist_id, prev_pl);
            else        strip_update();
        }
        tracks_append(r->items, r->n);

        if (!r->borrowed && ui.view_tracks && !ui.view_queue && !ui.view_dev && r->req == g_atomic_int_get(&tracks_req)) {
            char t[96];                                  /* loading indicator: grows as the pages arrive */
            snprintf(t, sizeof t, "Songs   (loading... %d so far)", r->offset + r->n);
            gtk_label_set_text(GTK_LABEL(ui.list_title), t);
        }

        if (r->offset == 0 && r->borrowed && view_restore(r->playlist_id))
            ui.tracks_centered = 1;                  /* back where you were in this playlist */

        if (!ui.tracks_centered) {
            if (strcmp(ui.tracks_pl, ui.context_id) == 0 && center_cards_on_current(r->offset == 0)) {
                ui.tracks_centered = 1;
                if (ui.view_tracks) select_current_track();
            } else if (r->offset == 0) {
                car_goto(0, 1);
            }
        }
        gtk_widget_queue_draw(ui.car);
    }

    if (!r->borrowed) free(r->items);
    g_free(r);
    return G_SOURCE_REMOVE;
}

static void start_tracks_load_n(const char *pid, int show_list, int attempt);
static void liked_check_start(void);

static gboolean tracks_retry_cb(gpointer data) {
    TrkResult *r = data;
    if (r->req == g_atomic_int_get(&tracks_req)) {    /* nothing newer was asked meanwhile */
        start_tracks_load_n(r->playlist_id, r->show_list, r->attempt);
    } else {
        char nm[256];
        playlist_name(r->playlist_id, nm, sizeof nm);
        activity_log(ACT_CANCELLED, "LOAD_PLAYLIST_SONGS", -1, "Replaced by a newer request before the retry",
                     "Playlist: %s (attempt %d)", nm, r->attempt + 1);
    }
    g_free(r);
    return G_SOURCE_REMOVE;
}

/* The whole answer (main thread). */
static gboolean tracks_done(gpointer data) {
    TrkResult *r = data;
    stall_trace('E', "tracks_done entered (req %d of %d)", r->req, g_atomic_int_get(&tracks_req));

    if (r->req != g_atomic_int_get(&tracks_req) || r->status == -3) {   /* replaced by a newer request */
        {   /* it used to vanish without a line: a lone [PENDING] then looked like a hang */
            char nm[256];
            playlist_name(r->playlist_id, nm, sizeof nm);
            activity_log(ACT_CANCELLED, "LOAD_PLAYLIST_SONGS", r->t0 ? (long)((g_get_monotonic_time() - r->t0) / 1000) : -1,
                         "Replaced by a newer request", "Playlist: %s (attempt %d) | %d songs were read", nm, r->attempt + 1, r->n);
        }
        stall_trace('F', "result removed: replaced by a newer request");
        free(r->items);
        g_free(r);
        return G_SOURCE_REMOVE;
    }
    ui.tracks_busy = 0;
    ui.tracks_loading[0] = '\0';
    stall_load_end();
    if (ui.view_tracks && !ui.view_queue && !ui.view_dev)          /* loading is over, whatever the result */
        gtk_label_set_text(GTK_LABEL(ui.list_title), "Songs   (T = back)");

    {   /* the result of the download, from what actually arrived */
        char nm[256], why[300];
        playlist_name(r->playlist_id, nm, sizeof nm);
        long ms = (long)((g_get_monotonic_time() - r->t0) / 1000);
        if (r->status == 200 && r->n > 0)
            activity_log(ACT_SUCCESS, "LOAD_PLAYLIST_SONGS", ms, NULL, "Playlist: %s | %d songs", nm, r->n);
        else if (r->status == 200)
            activity_log(ACT_WARNING, "LOAD_PLAYLIST_SONGS", ms, "Playlist has no readable songs", "Playlist: %s", nm);
        else {
            const char *e = explain(r->status);
            snprintf(why, sizeof why, "%s (HTTP %ld)%s", e ? e : "failed", r->status,
                     r->pages > 0 ? " - only part of the songs arrived" : "");
            activity_log(r->pages > 0 ? ACT_WARNING : ACT_FAILED, "LOAD_PLAYLIST_SONGS", ms, why,
                         "Playlist: %s | %d songs read | attempt %d", nm, r->n, r->attempt + 1);
        }
    }

    if (pls.want[0] && strcmp(pls.want, r->playlist_id) == 0 &&
        !(r->status == 200 && r->n > 0) && !r->pages &&
        (r->attempt >= 2 || r->status == 200 || r->status == 403 || r->status == 404)) {
        const char *why = r->status == 200 ? "has no songs" : "could not be loaded";   /* asked for with the switch */
        char name[256], msg[320];
        playlist_name(r->playlist_id, name, sizeof name);
        snprintf(msg, sizeof msg, "%s %s - still showing the previous playlist", name, why);
        set_status(msg);
        pls.want[0] = '\0';
    }

    if (r->status == 200 && r->n > 0) {                       /* complete: keep it for next time */
        PlCache *c = g_new0(PlCache, 1);
        c->items = r->items;                                   /* the cache owns the list now */
        c->n = r->n;
        c->at = g_get_monotonic_time() / G_USEC_PER_SEC;
        size_t bytes = sizeof(PlCache);
        if (!lru_mul((size_t)r->n, sizeof(TrackInfo), &bytes) || !lru_add(bytes, sizeof(PlCache), &bytes) ||
            !lru_put(plcache, r->playlist_id, c, bytes, NULL)) {
            g_free(c);                                         /* too big for the budget: shown, just not kept */
            player_log("[cache] playlist %s (%d songs) is larger than the playlist cache budget, not cached\n",
                       r->playlist_id, r->n);
        } else {
            r->items = NULL;                                   /* kept: the cache frees it */
        }
        strip_update();
    } else if (r->pages > 0) {
        set_status("Some songs could not be loaded - press T twice to try again");
    } else if (r->status != 200 && r->attempt < 2 && r->status != 403 && r->status != 404) {
        TrkResult *again = g_new0(TrkResult, 1);              /* temporary failure: try again shortly */
        snprintf(again->playlist_id, sizeof again->playlist_id, "%s", r->playlist_id);
        snprintf(again->name, sizeof again->name, "%s", r->name);
        again->show_list = r->show_list;
        again->req = r->req;
        again->attempt = r->attempt + 1;
        g_timeout_add(1500, tracks_retry_cb, again);
        ui.tracks_busy = 1;                                    /* still working on it */
        snprintf(ui.tracks_loading, sizeof ui.tracks_loading, "%s", r->playlist_id);
    } else if (r->show_list) {
        if (r->status != 200)
            set_status(r->status == 403 || r->status == 404
                           ? "Spotify won't show the songs of this playlist"
                           : explain(r->status));
        else
            set_status("No songs available - Spotify only lets this app read your own playlists");
    } else if (!car_mini) {
        /* the playing playlist can't be read: show previous / current / next */
        cards_reset();
        ui.tracks_pl[0] = '\0';
        g_atomic_int_set(&poll_reset, 1);
        gtk_widget_queue_draw(ui.car);
    }

    stall_trace('G', "playlist data processed (HTTP %ld, %d songs)", r->status, r->n);
    strip_update();                                            /* loading / icon state changed */
    stall_trace('H', "window updated");
    stall_trace('F', "result removed from the queue");
    stall_trace('I', "loading operation completed");
    free(r->items);
    g_free(r);
    return G_SOURCE_REMOVE;
}

typedef struct { int req; int pages; char pid[64]; int show_list; } TrkCtx;

static int tracks_page_cb(const TrackInfo *items, int n, int offset, void *c) {
    TrkCtx *x = c;
    if (x->req != g_atomic_int_get(&tracks_req)) return 1;     /* superseded: stop downloading */
    if (g_atomic_int_get(&app_closing)) return 1;              /* closing: stop downloading */
    if (!items || n <= 0) {                                    /* "still wanted?" question before a page request */
        stall_stage("waiting for Spotify: songs %d-%d", offset + 1, offset + 100);
        return 0;
    }
    stall_stage("page of %d songs received (offset %d), handing it to the window", n, offset);

    TrkResult *pg = g_new0(TrkResult, 1);
    pg->items = malloc((size_t)n * sizeof *pg->items);
    if (!pg->items) { g_free(pg); return 0; }
    memcpy(pg->items, items, (size_t)n * sizeof *pg->items);
    pg->n = n;
    pg->offset = offset;
    pg->req = x->req;
    pg->show_list = x->show_list;
    snprintf(pg->playlist_id, sizeof pg->playlist_id, "%s", x->pid);
    x->pages++;
    g_idle_add(tracks_page, pg);
    return 0;
}

static gpointer tracks_thread(gpointer data) {
    TrkResult *r = data;
    TrkCtx x = { r->req, 0, "", r->show_list };
    snprintf(x.pid, sizeof x.pid, "%s", r->playlist_id);
    r->t0 = g_get_monotonic_time();
    { const char *nm = r->name;
      activity_log(ACT_PENDING, "LOAD_PLAYLIST_SONGS", -1, NULL, "Playlist: %s (attempt %d)", nm, r->attempt + 1);
      stall_load_begin(nm);
      stall_stage("waiting for Spotify: songs 1-100 (attempt %d)", r->attempt + 1); }

    r->status = player_fetch_playlist_pages(r->playlist_id, &r->items, &r->n, tracks_page_cb, &x);
    r->pages = x.pages;
    stall_trace('A', "download completed (HTTP %ld, %d songs, %d pages)", r->status, r->n, r->pages);
    stall_stage("download finished (HTTP %ld, %d songs), waiting for the window to take the result", r->status, r->n);
    stall_trace('C', "result queued for the window (req %d)", r->req);
    g_idle_add(tracks_done, r);
    stall_trace('D', "main-loop callback scheduled (tracks_done)");
    return NULL;
}

/* ---- Liked Songs changes all the time (you like / unlike while listening), a playlist rarely does. The kept
 * list is shown instantly, then ONE small request (count + newest song) tells whether it is still right; only if
 * not is it marked out of date and read again. At most one check per 20 s. ---- */
#define LIKED_CHECK_EVERY_S 20
static gint64 liked_checked_at;
static int    liked_check_busy;
typedef struct { long status; int total; char first[96]; gint64 t0; } LikedHead;

static gboolean liked_check_done(gpointer data) {
    LikedHead *h = data;
    liked_check_busy = 0;
    long ms = (long)((g_get_monotonic_time() - h->t0) / 1000);
    PlCache *c = plcache ? lru_find(plcache, LIKED_ID) : NULL;
    if (h->status != 200) {
        activity_log(ACT_WARNING, "LIKED_SONGS_CHECK", ms, "Could not ask Spotify (HTTP %ld): the kept list is shown unchanged",
                     "Liked Songs");
    } else if (c && !c->stale) {
        int expect = h->total > 2000 ? 2000 : h->total;       /* the list is read up to 2000 songs */
        int changed = h->total >= 0 && c->n != expect;
        if (!changed && c->n > 0 && h->first[0] && strcmp(c->items[0].uri, h->first) != 0) changed = 1;
        if (changed) {
            c->stale = 1;
            activity_log(ACT_SUCCESS, "LIKED_SONGS_CHANGED", ms, NULL,
                         "Liked Songs changed on Spotify (kept %d songs, now %d) | reading it again", c->n, h->total);
            if (strcmp(ui.tracks_pl, LIKED_ID) == 0 && !ui.tracks_busy)
                start_tracks_load_n(LIKED_ID, ui.view_tracks, 0);
        }
    }
    g_free(h);
    return G_SOURCE_REMOVE;
}

static gpointer liked_check_thread(gpointer data) {
    LikedHead *h = data;
    h->status = player_liked_head(h->first, sizeof h->first, &h->total);
    g_idle_add(liked_check_done, h);
    return NULL;
}

static void liked_check_start(void) {
    gint64 now = g_get_monotonic_time();
    if (liked_check_busy || (liked_checked_at && now - liked_checked_at < (gint64)LIKED_CHECK_EVERY_S * G_USEC_PER_SEC))
        return;
    liked_check_busy = 1;
    liked_checked_at = now;
    LikedHead *h = g_new0(LikedHead, 1);
    h->t0 = now;
    GThread *t = g_thread_new("liked-check", liked_check_thread, h);
    g_thread_unref(t);
}

static void start_tracks_load_n(const char *pid, int show_list, int attempt) {
    int req = g_atomic_int_add(&tracks_req, 1) + 1;            /* older requests stop being valid */
    ui.tracks_busy = 1;
    snprintf(ui.tracks_loading, sizeof ui.tracks_loading, "%s", pid);

    PlCache *c = plcache ? lru_get(plcache, pid) : NULL;
    if (c && attempt == 0 && !c->stale &&
        (view_restore_force || g_get_monotonic_time() / G_USEC_PER_SEC - c->at < PLCACHE_FRESH)) {
        TrkResult *pg = g_new0(TrkResult, 1);                  /* seen lately: show it right now */
        pg->items = c->items;                                  /* no copy: the cache keeps the list */
        pg->borrowed = 1;
        pg->n = c->n;
        pg->req = req;
        pg->show_list = show_list;
        snprintf(pg->playlist_id, sizeof pg->playlist_id, "%s", pid);
        { char nm[256]; playlist_name(pid, nm, sizeof nm);
          activity_log(ACT_SUCCESS, "LOAD_PLAYLIST_SONGS", 0, NULL, "Playlist: %s | %d songs | from memory (no download)", nm, c->n); }
        tracks_page(pg);                                       /* (does not free borrowed items) */
        stall_load_end();                                      /* a newer request replaced any download still running */
        ui.tracks_busy = 0;
        ui.tracks_loading[0] = '\0';
        if (strcmp(pid, LIKED_ID) == 0) liked_check_start();   /* shown at once; one tiny request checks it is still right */
        return;
    }
    if (strcmp(pid, LIKED_ID) == 0) liked_checked_at = g_get_monotonic_time();   /* a full read is as good as a check */

    TrkResult *r = g_new0(TrkResult, 1);
    snprintf(r->playlist_id, sizeof r->playlist_id, "%s", pid);
    playlist_name(pid, r->name, sizeof r->name);          /* main thread: safe to read the GTK list here */
    r->show_list = show_list;
    r->req = req;
    r->attempt = attempt;
    stall_trace('B', "result object created (req %d, attempt %d)", req, attempt + 1);

    GThread *t = g_thread_new("tracks", tracks_thread, r);
    g_thread_unref(t);
}

static void start_tracks_load(const char *pid, int show_list) {
    start_tracks_load_n(pid, show_list, 0);
}

static void close_queue_view(void);
static void close_devices_view(void);

static void toggle_tracks_view(void) {
    if (!ui.logged_in) return;
    if (ui.view_dev) close_devices_view();
    if (ui.view_queue) close_queue_view();

    if (ui.view_tracks) {                       /* back to the playlists */
        ui.view_tracks = 0;
        if (ui.shuffle) g_atomic_int_set(&poll_reset, 1);   /* redraw the shuffle order */
        gtk_tree_view_set_model(GTK_TREE_VIEW(ui.tree), GTK_TREE_MODEL(ui.store));
        gtk_label_set_text(GTK_LABEL(ui.list_title), "Your playlists");
        select_row_by_id(ui.store, ui.sel_pl, TRUE);
        set_status("Playlists");
        activity_log(ACT_SUCCESS, "NAVIGATE_PAGE", -1, NULL, "Page: Playlists");
        return;
    }

    set_list_open(1);

    /* Open the highlighted playlist (not necessarily the playing one). */
    ui.sel_pl[0] = '\0';
    remember_playlist_selection();
    const char *pid = ui.sel_pl[0] ? ui.sel_pl : ui.context_id;
    if (!pid[0]) {
        set_status("Pick a playlist first (Up / Down)");
        return;
    }

    if (strcmp(pid, ui.tracks_pl) == 0 && cn > 0 && !car_mini) {   /* loaded, or loading right now */
        show_tracks_view(pid);
        return;
    }
    if (ui.tracks_busy && strcmp(pid, ui.tracks_loading) == 0) {   /* same one: show it when page 1 lands */
        ui.tracks_show_when_ready = 1;
        set_status("Loading songs...");
        return;
    }

    set_status("Loading songs...");
    { char nm[256]; playlist_name(pid, nm, sizeof nm);
      activity_log(ACT_SUCCESS, "NAVIGATE_PAGE", -1, NULL, "Page: Songs of %s (loading)", nm); }
    start_tracks_load(pid, 1);
}

static void play_selected_track(void) {
    if (!ui.logged_in) return;

    GtkTreeSelection *sel = gtk_tree_view_get_selection(GTK_TREE_VIEW(ui.tree));
    GtkTreeIter it;
    if (!gtk_tree_selection_get_selected(sel, NULL, &it)) {
        set_status("Pick a song first (Up / Down)");
        return;
    }

    gchar *name = NULL, *uri = NULL;
    gtk_tree_model_get(GTK_TREE_MODEL(ui.tracks), &it, 0, &name, 1, &uri, -1);

    Job *j = g_new0(Job, 1);
    j->track = 1;
    snprintf(j->id, sizeof j->id, "%s", ui.tracks_pl);
    snprintf(j->uri, sizeof j->uri, "%s", uri ? uri : "");
    snprintf(j->okmsg, sizeof j->okmsg, "Playing: %s", name ? name : "");
    select_song(j, j->uri, name ? name : "", NULL, NULL);

    g_free(name);
    g_free(uri);
}

static void play_on_selected_device(void);

static void activate_selected(void) {
    if (ui.view_dev) { play_on_selected_device(); return; }
    if (ui.view_queue) return;               /* the queue is only for viewing / dragging */
    if (ui.view_tracks) play_selected_track();
    else                play_selected();
}

/* ---------- login ---------- */

static gboolean auth_done(gpointer data) {
    if (GPOINTER_TO_INT(data) != 0) {
        set_status("Login failed - close the app and try again");
        return G_SOURCE_REMOVE;
    }

    ui.logged_in = 1;
    set_status("Logged in");
    load_playlists();
    poll_now();
    poll_arm(poll_want_ms());                /* a window that is hidden at login starts slow */
    return G_SOURCE_REMOVE;
}

static gpointer auth_thread(gpointer data) {
    gint64 t0 = g_get_monotonic_time();
    activity_log(ACT_PENDING, "LOGIN", -1, NULL, "Spotify account (token check / browser sign-in)");
    g_mutex_lock(&api_lock);
    int rc = auth_init();           /* may open the browser and wait */
    g_mutex_unlock(&api_lock);
    long ms = (long)((g_get_monotonic_time() - t0) / 1000);
    if (rc == 0) activity_log(ACT_SUCCESS, "LOGIN", ms, NULL, "Spotify account");
    else         activity_log(ACT_FAILED, "LOGIN", ms, "Sign-in was cancelled, denied, or the token could not be obtained",
                              "Spotify account");
    g_idle_add(auth_done, GINT_TO_POINTER(rc));
    return NULL;
}

/* ---------- keyboard ---------- */

/* ---------- queue view (6 = open, 7 = close, drag rows to reorder) ---------- */

typedef struct {
    TrackBrief *items;
    int         n;
    long        status;
} QueueResult;

static char q_orig[24][96];       /* order Spotify has right now, to spot real changes */
static int  q_orig_n;

static void update_queue_btn(void) {
    GtkStyleContext *sc = gtk_widget_get_style_context(ui.queue_btn);
    gtk_button_set_label(GTK_BUTTON(ui.queue_btn),
                         ui.view_queue ? "Close queue  (A)" : "Open queue  (A)");
    if (ui.view_queue) gtk_style_context_add_class(sc, "on");
    else               gtk_style_context_remove_class(sc, "on");
}

/* Last queue seen: shown the moment the view opens, then refreshed in the background. */
static TrackBrief qcache[24];
static int        qcache_n = -1;                 /* -1 = nothing cached yet */

static void fill_queue_store(const TrackBrief *items, int n) {
    int same = (n == q_orig_n && n == gtk_tree_model_iter_n_children(GTK_TREE_MODEL(ui.queue), NULL));
    for (int i = 0; same && i < n && i < 24; i++)
        if (strcmp(q_orig[i], items[i].uri) != 0) same = 0;
    if (same) return;                            /* nothing changed: leave the list alone (no flicker) */

    ui.queue_filling = 1;
    gtk_list_store_clear(ui.queue);
    for (int i = 0; i < n; i++) {
        char line[540];
        snprintf(line, sizeof line, "%s  -  %s", items[i].name, items[i].artist);
        GtkTreeIter it;
        gtk_list_store_append(ui.queue, &it);
        gtk_list_store_set(ui.queue, &it, 0, line, 1, items[i].uri, -1);
    }
    ui.queue_filling = 0;
    q_orig_n = n < 24 ? n : 24;
    for (int i = 0; i < q_orig_n; i++)
        snprintf(q_orig[i], sizeof q_orig[i], "%s", items[i].uri);
}

static gboolean queue_loaded(gpointer data) {
    QueueResult *r = data;

    if (r->status != 200) {
        const char *err = explain(r->status);
        set_status(err ? err : "Could not load the queue");
        char why[300];
        snprintf(why, sizeof why, "%s (HTTP %ld)", err ? err : "failed", r->status);
        activity_log(ACT_FAILED, "LOAD_QUEUE", -1, why, "Up Next list");
    } else {
        activity_log(ACT_SUCCESS, "LOAD_QUEUE", -1, NULL, "%d upcoming song%s", r->n, r->n == 1 ? "" : "s");
        qcache_n = r->n < 24 ? r->n : 24;                 /* remember it for the next opening */
        memcpy(qcache, r->items, (size_t)qcache_n * sizeof *qcache);
    }
    if (r->status == 200 && ui.view_queue) {
        fill_queue_store(r->items, r->n);
        set_status(r->n ? "Drag songs to change the order - 7 to close"
                        : "The queue is empty - press Q on a song to add one");
    }

    free(r->items);
    g_free(r);
    return G_SOURCE_REMOVE;
}

static gpointer queue_thread(gpointer unused) {
    QueueResult *r = g_new0(QueueResult, 1);
    r->items = calloc(24, sizeof *r->items);
    if (!r->items) activity_log(ACT_FAILED, "MEMORY_ALLOC", -1, "calloc returned NULL", "Queue list buffer");

    r->status = r->items ? player_get_queue_n(r->items, 24, &r->n) : -1;

    g_idle_add(queue_loaded, r);
    return NULL;
}

static void close_devices_view(void);

/* ---- "Now playing" card above the upcoming songs ---- */

static guint np_fade_id;
static int   np_fade_step;

static gboolean np_fade_cb(gpointer unused) {
    np_fade_step++;
    double o = 0.25 + 0.0938 * np_fade_step;           /* ~0.25 -> 1.0 in 8 steps */
    gtk_widget_set_opacity(ui.np_box, o > 1.0 ? 1.0 : o);
    if (np_fade_step >= 8) { np_fade_id = 0; return G_SOURCE_REMOVE; }
    return G_SOURCE_CONTINUE;
}

static void np_fade(void) {
    np_fade_step = 0;
    gtk_widget_set_opacity(ui.np_box, 0.25);
    if (!np_fade_id) np_fade_id = g_timeout_add(28, np_fade_cb, NULL);
}

static void np_update(int changed) {
    if (!ui.view_queue || !ui.np_box) return;

    if (ui.np_uri[0]) {
        char *m = g_markup_printf_escaped("<span weight=\"bold\" size=\"large\">%s</span>", ui.np_name);
        label_markup_once(ui.np_title, m);
        g_free(m);
        label_text_once(ui.np_artist, ui.np_artist_s);
        label_text_once(ui.np_status, ui.playing ? "Playing" : "Paused");
    } else {
        label_markup_once(ui.np_title,
            "<span weight=\"bold\" size=\"large\">Nothing playing</span>");
        label_text_once(ui.np_artist, "");
        label_text_once(ui.np_status, "");
    }

    GdkPixbuf *pb = art_lookup(ui.np_img_url);         /* album picture */
    if (pb) {
        if (strcmp(ui.np_img_set, ui.np_img_url) != 0) {
            GdkPixbuf *sc = gdk_pixbuf_scale_simple(pb, 72, 72, GDK_INTERP_BILINEAR);
            if (sc) {
                gtk_image_set_from_pixbuf(GTK_IMAGE(ui.np_img), sc);
                g_object_unref(sc);
                snprintf(ui.np_img_set, sizeof ui.np_img_set, "%s", ui.np_img_url);
            }
        }
    } else if (ui.np_img_set[0] || !gtk_image_get_pixbuf(GTK_IMAGE(ui.np_img))) {
        GdkPixbuf *ph = placeholder_pixbuf();               /* clean fallback while / if no cover */
        if (ph) gtk_image_set_from_pixbuf(GTK_IMAGE(ui.np_img), ph);
        ui.np_img_set[0] = '\0';
    }

    if (!changed) return;

    np_fade();
    /* the song that was first in "Up Next" moves up into the card */
    GtkTreeModel *m = GTK_TREE_MODEL(ui.queue);
    GtkTreeIter it;
    if (ui.np_uri[0] && gtk_tree_model_get_iter_first(m, &it)) {
        gchar *uri = NULL;
        gtk_tree_model_get(m, &it, 1, &uri, -1);
        if (uri && strcmp(uri, ui.np_uri) == 0) {
            ui.queue_filling = 1;                      /* not a drag: do not reorder */
            gtk_list_store_remove(ui.queue, &it);
            ui.queue_filling = 0;
            if (q_orig_n > 0) {
                memmove(q_orig[0], q_orig[1], (size_t)(q_orig_n - 1) * sizeof q_orig[0]);
                q_orig_n--;
            }
        }
        g_free(uri);
    }
    g_timeout_add(900, queue_reload_cb, NULL);         /* then refresh the rest */
}

static void open_queue_view(void) {
    if (!ui.logged_in || ui.view_queue) return;
    set_list_open(1);
    if (ui.view_dev) close_devices_view();

    ui.view_queue = 1;
    activity_log(ACT_SUCCESS, "OPEN_PANEL", -1, NULL, "Panel: Queue (Up Next)");
    update_queue_btn();
    if (qcache_n >= 0) {
        q_orig_n = -1;                                    /* force the cached rows to be drawn */
        fill_queue_store(qcache, qcache_n);               /* instant: last known queue */
    } else {
        ui.queue_filling = 1;
        gtk_list_store_clear(ui.queue);
        ui.queue_filling = 0;
    }
    gtk_tree_view_set_model(GTK_TREE_VIEW(ui.tree), GTK_TREE_MODEL(ui.queue));
    gtk_tree_view_set_reorderable(GTK_TREE_VIEW(ui.tree), TRUE);
    gtk_label_set_text(GTK_LABEL(ui.list_title), "Up Next   (drag to reorder)");
    gtk_widget_show(ui.np_box);
    np_update(0);
    set_status(qcache_n >= 0 ? "Updating the queue..." : "Loading the queue...");

    GThread *t = g_thread_new("queue", queue_thread, NULL);
    g_thread_unref(t);
}

static gboolean apply_queue_order(gpointer unused);

static void close_queue_view(void) {
    if (!ui.view_queue) return;

    if (ui.queue_timer) {                    /* a change is still waiting: apply it now */
        g_source_remove(ui.queue_timer);
        apply_queue_order(NULL);
    }
    ui.view_queue = 0;
    activity_log(ACT_SUCCESS, "CLOSE_PANEL", -1, NULL, "Panel: Queue (Up Next)");
    update_queue_btn();
    gtk_widget_hide(ui.np_box);
    gtk_tree_view_set_reorderable(GTK_TREE_VIEW(ui.tree), FALSE);

    if (ui.view_tracks) {
        gtk_tree_view_set_model(GTK_TREE_VIEW(ui.tree), GTK_TREE_MODEL(ui.tracks));
        gtk_label_set_text(GTK_LABEL(ui.list_title), "Songs   (T = back)");
        select_current_track();
    } else {
        gtk_tree_view_set_model(GTK_TREE_VIEW(ui.tree), GTK_TREE_MODEL(ui.store));
        gtk_label_set_text(GTK_LABEL(ui.list_title), "Your playlists");
        select_row_by_id(ui.store, ui.sel_pl, TRUE);
    }
    set_status("Queue closed");
}

static void toggle_queue_view(void) {
    if (ui.view_queue) close_queue_view();
    else               open_queue_view();
}

/* Spotify cannot move queue items, so the new order is sent as a list that starts
 * with the song playing right now. That song is kept at its live position and in its
 * play / pause state, and nothing is sent when the order did not really change. */
typedef struct {
    char uris[24][96];
    int  n;
    long status;
} QApply;

static gboolean queue_apply_done(gpointer data) {
    QApply *q = data;

    if (q->status >= 200 && q->status < 300) {
        activity_log(ACT_SUCCESS, "QUEUE_REORDER", -1, NULL, "%d songs in the new order", q->n);
        set_status("Queue order updated - playback kept going");
        g_timeout_add(500, poll_once_cb, NULL);
    } else if (q->status == -3) {
        activity_log(ACT_WARNING, "QUEUE_REORDER", -1, "Nothing is playing - the new order was not applied", "%d songs", q->n);
        set_status("Nothing is playing - the new order was not applied");
    } else {
        const char *err = explain(q->status);
        char m[160];
        activity_log(ACT_FAILED, "QUEUE_REORDER", -1, err ? err : "failed", "%d songs (HTTP %ld)", q->n, q->status);
        snprintf(m, sizeof m, "Could not update the queue: %s (HTTP %ld)",
                 err ? err : "failed", q->status);
        set_status(m);
    }
    g_free(q);
    return G_SOURCE_REMOVE;
}

static gpointer queue_apply_thread(gpointer data) {
    QApply *q = data;
    char (*u)[96] = calloc(25, sizeof *u);
    if (!u) activity_log(ACT_FAILED, "MEMORY_ALLOC", -1, "calloc returned NULL", "Queue reorder buffer");

    g_mutex_lock(&api_lock);
    PlayerState st;
    gint64 t0 = g_get_monotonic_time();
    long gs = player_get_state(&st);

    if (!u) {
        q->status = -1;
    } else if (gs != 200 || !st.active || !st.track_uri[0]) {
        q->status = gs == 200 ? -3 : gs;
    } else {
        int n = 0;
        snprintf(u[n++], sizeof u[0], "%s", st.track_uri);
        for (int i = 0; i < q->n && n < 25; i++)
            if (strcmp(q->uris[i], st.track_uri) != 0)
                snprintf(u[n++], sizeof u[0], "%s", q->uris[i]);

        /* where the song is now: the position we read + time spent since */
        long pos = st.progress_ms + (long)((g_get_monotonic_time() - t0) / 1000) + 250;
        if (st.duration_ms > 0 && pos >= st.duration_ms) pos = st.duration_ms - 500;
        if (pos < 0) pos = 0;

        q->status = player_play_uris_at(u, n, pos);
        if (q->status >= 200 && q->status < 300 && !st.playing)
            player_http_cmd("PUT", "/pause");           /* it was paused: keep it paused */
    }
    g_mutex_unlock(&api_lock);

    free(u);
    g_idle_add(queue_apply_done, q);
    return NULL;
}

static gboolean apply_queue_order(gpointer unused) {
    ui.queue_timer = 0;
    if (!ui.view_queue) return G_SOURCE_REMOVE;

    QApply *q = g_new0(QApply, 1);
    GtkTreeModel *m = GTK_TREE_MODEL(ui.queue);
    GtkTreeIter it;
    if (gtk_tree_model_get_iter_first(m, &it)) {
        do {
            gchar *uri = NULL;
            gtk_tree_model_get(m, &it, 1, &uri, -1);
            if (uri && q->n < 24) snprintf(q->uris[q->n++], sizeof q->uris[0], "%s", uri);
            g_free(uri);
        } while (gtk_tree_model_iter_next(m, &it));
    }

    int same = q->n == q_orig_n;                    /* dropped back where it was: do nothing */
    for (int i = 0; same && i < q->n; i++)
        if (strcmp(q->uris[i], q_orig[i]) != 0) same = 0;
    if (same || q->n == 0) {
        g_free(q);
        return G_SOURCE_REMOVE;
    }

    q_orig_n = q->n;                                /* this is the order Spotify will have */
    for (int i = 0; i < q->n; i++)
        snprintf(q_orig[i], sizeof q_orig[i], "%s", q->uris[i]);

    GThread *t = g_thread_new("queueapply", queue_apply_thread, q);
    g_thread_unref(t);
    return G_SOURCE_REMOVE;
}

/* A drag-and-drop move ends with a row being deleted from the list. */
static void on_queue_row_deleted(GtkTreeModel *m, GtkTreePath *p, gpointer unused) {
    if (ui.queue_filling || !ui.view_queue) return;
    if (ui.queue_timer) g_source_remove(ui.queue_timer);
    ui.queue_timer = g_timeout_add(400, apply_queue_order, NULL);
}

/* ---------- devices (V key): play on a logged-in device that is not playing ---------- */

typedef struct {
    DeviceInfo list[16];
    int        n;
    long       status;
} DevRes;

static gboolean devices_loaded(gpointer data) {
    DevRes *r = data;

    if (!ui.view_dev) {                       /* closed while loading */
        g_free(r);
        return G_SOURCE_REMOVE;
    }

    if (r->status != 200) {
        const char *err = explain(r->status);
        set_status(err ? err : "Could not load your devices");
        activity_log(ACT_FAILED, "LOAD_DEVICES", -1, err ? err : "failed", "Spotify devices (HTTP %ld)", r->status);
        g_free(r);
        return G_SOURCE_REMOVE;
    }
    activity_log(r->n > 0 ? ACT_SUCCESS : ACT_WARNING, "LOAD_DEVICES", -1, r->n > 0 ? NULL : "No device is open",
                 "%d device%s", r->n, r->n == 1 ? "" : "s");

    gtk_list_store_clear(ui.devs);
    GtkTreeIter first_ok;
    int have_ok = 0;

    for (int i = 0; i < r->n; i++) {
        const DeviceInfo *d = &r->list[i];
        int playing_now = d->active && ui.playing;     /* never interrupt this one */
        int eligible = !d->restricted && !playing_now;

        const char *state = d->restricted ? "cannot be controlled remotely"
                          : playing_now   ? "playing now (will not be interrupted)"
                          : d->active     ? "paused"
                                          : "idle";
        char line[300];
        snprintf(line, sizeof line, "%s   (%s)   -   %s", d->name, d->type, state);

        GtkTreeIter it;
        gtk_list_store_append(ui.devs, &it);
        gtk_list_store_set(ui.devs, &it, 0, line, 1, d->id, 2, eligible, 3, d->name, -1);
        if (eligible && !have_ok) { first_ok = it; have_ok = 1; }
    }

    if (have_ok)
        gtk_tree_selection_select_iter(
            gtk_tree_view_get_selection(GTK_TREE_VIEW(ui.tree)), &first_ok);

    if (r->n == 0)
        set_status("No devices found - open Spotify on a device that is logged in to your account");
    else if (!have_ok)
        set_status("No idle device available right now");
    else
        set_status("Pick a device, then Enter or the Play button");

    g_free(r);
    return G_SOURCE_REMOVE;
}

static gpointer devices_thread(gpointer unused) {
    DevRes *r = g_new0(DevRes, 1);
    r->status = player_list_devices(r->list, 16, &r->n);
    g_idle_add(devices_loaded, r);
    return NULL;
}

static void refresh_devices(void) {
    GThread *t = g_thread_new("devices", devices_thread, NULL);
    g_thread_unref(t);
}

static void open_devices_view(void) {
    if (!ui.logged_in || ui.view_dev) return;
    set_list_open(1);
    if (ui.view_queue) close_queue_view();

    ui.view_dev = 1;
    activity_log(ACT_SUCCESS, "OPEN_PANEL", -1, NULL, "Panel: Devices");
    gtk_list_store_clear(ui.devs);
    gtk_tree_view_set_model(GTK_TREE_VIEW(ui.tree), GTK_TREE_MODEL(ui.devs));
    gtk_label_set_text(GTK_LABEL(ui.list_title), "Devices   (V = close)");
    gtk_widget_show(ui.dev_btn);
    set_status("Looking for your devices...");
    refresh_devices();
}

static void close_devices_view(void) {
    if (!ui.view_dev) return;
    ui.view_dev = 0;
    activity_log(ACT_SUCCESS, "CLOSE_PANEL", -1, NULL, "Panel: Devices");
    gtk_widget_hide(ui.dev_btn);

    if (ui.view_tracks) {
        gtk_tree_view_set_model(GTK_TREE_VIEW(ui.tree), GTK_TREE_MODEL(ui.tracks));
        gtk_label_set_text(GTK_LABEL(ui.list_title), "Songs   (T = back)");
        select_current_track();
    } else {
        gtk_tree_view_set_model(GTK_TREE_VIEW(ui.tree), GTK_TREE_MODEL(ui.store));
        gtk_label_set_text(GTK_LABEL(ui.list_title), "Your playlists");
        select_row_by_id(ui.store, ui.sel_pl, TRUE);
    }
    set_status("Devices closed");
}

typedef struct {
    char id[64], name[96], uri[96], song[256];
    long status;
    int  verified;
} DevPlay;

static gboolean dev_play_done(gpointer data) {
    DevPlay *j = data;
    ui.dev_busy = 0;

    char m[400];
    activity_log(j->status >= 200 && j->status < 300 ? (j->verified ? ACT_SUCCESS : ACT_WARNING) : ACT_FAILED,
                 "PLAY_ON_DEVICE", -1,
                 j->status >= 200 && j->status < 300 ? (j->verified ? NULL : "Sent, but the device is not playing yet")
                                                      : (explain(j->status) ? explain(j->status) : "failed"),
                 "Device: %s | Song: %s", j->name, j->song);
    if (j->status >= 200 && j->status < 300) {
        if (j->verified)
            snprintf(m, sizeof m, "Playing \"%s\" on %s", j->song, j->name);
        else
            snprintf(m, sizeof m, "Sent to %s, but it is not playing yet - check that device", j->name);
    } else if (j->status == 404) {
        snprintf(m, sizeof m, "%s is not available any more - list refreshed", j->name);
    } else if (j->status == 403) {
        snprintf(m, sizeof m, "%s refused the command (Premium needed, or the device is restricted)", j->name);
    } else {
        const char *err = explain(j->status);
        snprintf(m, sizeof m, "Could not play on %s: %s (HTTP %ld)", j->name,
                 err ? err : "failed", j->status);
    }
    set_status(m);

    g_atomic_int_set(&poll_reset, 1);
    g_timeout_add(300, poll_once_cb, NULL);   /* show the new playback immediately */
    if (ui.view_dev) refresh_devices();
    g_free(j);
    return G_SOURCE_REMOVE;
}

static gpointer dev_play_thread(gpointer data) {
    DevPlay *j = data;

    g_mutex_lock(&api_lock);
    j->status = player_play_on_device(j->id, j->uri);
    g_mutex_unlock(&api_lock);

    if (j->status >= 200 && j->status < 300) {     /* check that it really started */
        for (int tries = 0; tries < 8 && !j->verified; tries++) {
            g_usleep(500000);
            PlayerState st;
            g_mutex_lock(&api_lock);
            long gs = player_get_state(&st);
            g_mutex_unlock(&api_lock);
            if (gs == 200 && st.active && st.playing &&
                strcmp(st.device_name, j->name) == 0 &&
                strcmp(st.track_uri, j->uri) == 0)
                j->verified = 1;
        }
    }
    fprintf(stderr, "[devices] play on %s: HTTP %ld verified=%d\n", j->name, j->status, j->verified);
    g_idle_add(dev_play_done, j);
    return NULL;
}

static void play_on_selected_device(void) {
    if (!ui.logged_in || !ui.view_dev) return;
    if (ui.dev_busy) { set_status("Already starting playback - please wait"); return; }

    GtkTreeModel *m;
    GtkTreeIter it;
    if (!gtk_tree_selection_get_selected(
            gtk_tree_view_get_selection(GTK_TREE_VIEW(ui.tree)), &m, &it)) {
        set_status("Pick a device first (Up / Down)");
        return;
    }

    gchar *id = NULL, *name = NULL;
    gint eligible = 0;
    gtk_tree_model_get(m, &it, 1, &id, 2, &eligible, 3, &name, -1);

    /* the song: the middle one of the carousel, otherwise the one playing */
    const char *uri = NULL, *song = "";
    if (cn > 0) {
        int mid = (int)floor(car_cx + 0.5);
        if (mid < 0) mid = 0;
        if (mid > cn - 1) mid = cn - 1;
        uri = citems[mid].uri;
        song = citems[mid].name;
    } else if (ui.current_uri[0]) {
        uri = ui.current_uri;
    }

    if (!id || !name) {
        set_status("Pick a device first (Up / Down)");
    } else if (!eligible) {
        set_status("That device cannot be used now - it is playing already or is restricted");
    } else if (!uri || !*uri) {
        set_status("Pick a song first - scroll the pictures to the song you want");
    } else {
        DevPlay *j = g_new0(DevPlay, 1);
        snprintf(j->id, sizeof j->id, "%s", id);
        snprintf(j->name, sizeof j->name, "%s", name);
        snprintf(j->uri, sizeof j->uri, "%s", uri);
        snprintf(j->song, sizeof j->song, "%s", song);
        ui.dev_busy = 1;
        set_status("Starting playback on that device...");
        GThread *t = g_thread_new("devplay", dev_play_thread, j);
        g_thread_unref(t);
    }
    g_free(id);
    g_free(name);
}

/* ---------- ambient background that follows the album artwork ---------- */

#define BG_BASE 0.07

static void rgb_to_hsv(double r, double g, double b, double *h, double *s, double *v) {
    double mx = fmax(r, fmax(g, b)), mn = fmin(r, fmin(g, b)), d = mx - mn;
    *v = mx;
    *s = mx > 0 ? d / mx : 0;
    double hh = 0;
    if (d > 0) {
        if (mx == r)      hh = fmod((g - b) / d, 6.0);
        else if (mx == g) hh = (b - r) / d + 2.0;
        else              hh = (r - g) / d + 4.0;
        hh *= 60.0;
        if (hh < 0) hh += 360.0;
    }
    *h = hh;
}

static void hsv_to_rgb(double h, double s, double v, double *r, double *g, double *b) {
    double c = v * s, x = c * (1 - fabs(fmod(h / 60.0, 2.0) - 1)), m = v - c;
    double rr = 0, gg = 0, bb = 0;
    int k = (int)(h / 60.0) % 6;
    switch (k) {
    case 0: rr = c; gg = x; break;
    case 1: rr = x; gg = c; break;
    case 2: gg = c; bb = x; break;
    case 3: gg = x; bb = c; break;
    case 4: rr = x; bb = c; break;
    default: rr = c; bb = x; break;
    }
    *r = rr + m; *g = gg + m; *b = bb + m;
}

/* Finds up to 3 different dominant colors of the picture and darkens them. */
static void bg_extract(GdkPixbuf *pb, double out[3][3]) {
    GdkPixbuf *sm = gdk_pixbuf_scale_simple(pb, 32, 32, GDK_INTERP_BILINEAR);
    for (int i = 0; i < 3; i++) out[i][0] = out[i][1] = out[i][2] = BG_BASE;
    if (!sm) return;

    int nc = gdk_pixbuf_get_n_channels(sm), rs = gdk_pixbuf_get_rowstride(sm);
    const guchar *px = gdk_pixbuf_get_pixels(sm);

    double w[24] = {0}, sr[24] = {0}, sg[24] = {0}, sb[24] = {0};
    for (int y = 0; y < 32; y++) {
        for (int x = 0; x < 32; x++) {
            const guchar *p = px + y * rs + x * nc;
            double r = p[0] / 255.0, g = p[1] / 255.0, b = p[2] / 255.0, h, sa, v;
            rgb_to_hsv(r, g, b, &h, &sa, &v);
            if (v < 0.12) continue;                         /* near black */
            int bin = ((int)(h / 30.0) % 12) * 2 + (sa > 0.4 ? 1 : 0);
            double wt = (0.15 + sa) * (0.3 + v);
            w[bin] += wt; sr[bin] += r * wt; sg[bin] += g * wt; sb[bin] += b * wt;
        }
    }
    g_object_unref(sm);

    double col[3][3];
    int np = 0;
    for (int round = 0; round < 3; round++) {
        int best = -1;
        double bw = 0;
        for (int i = 0; i < 24; i++) {
            if (w[i] <= bw) continue;
            double r = sr[i] / w[i], g = sg[i] / w[i], b = sb[i] / w[i];
            int ok = 1;                                       /* must differ from the ones taken */
            for (int k = 0; k < np && ok; k++) {
                double dr = r - col[k][0], dg = g - col[k][1], db = b - col[k][2];
                if (dr * dr + dg * dg + db * db < 0.09) ok = 0;
            }
            if (ok) { best = i; bw = w[i]; }
        }
        if (best < 0) break;
        col[np][0] = sr[best] / w[best];
        col[np][1] = sg[best] / w[best];
        col[np][2] = sb[best] / w[best];
        np++;
    }
    if (np == 0) return;                                      /* dark / empty art: default */
    for (int i = np; i < 3; i++) {                            /* few colors: neighbours of the main one */
        double h, s, v;
        rgb_to_hsv(col[0][0], col[0][1], col[0][2], &h, &s, &v);
        h = fmod(h + (i == 1 ? 28.0 : 332.0), 360.0);
        s *= 0.8;
        v *= (i == 1 ? 0.85 : 0.7);
        hsv_to_rgb(h, s, v, &col[i][0], &col[i][1], &col[i][2]);
    }

    for (int i = 0; i < 3; i++) {                             /* keep it dark and calm */
        double h, s, v, r, g, b;
        rgb_to_hsv(col[i][0], col[i][1], col[i][2], &h, &s, &v);
        if (s > 0.8) s = 0.8;
        v = 0.20 + 0.34 * v;                                  /* 0.20 - 0.54 */
        hsv_to_rgb(h, s, v, &r, &g, &b);
        double lum = 0.2126 * r + 0.7152 * g + 0.0722 * b;    /* never too bright for white text */
        if (lum > 0.32) { double f = 0.32 / lum; r *= f; g *= f; b *= f; }
        if (!isfinite(r) || !isfinite(g) || !isfinite(b)) r = g = b = BG_BASE;
        out[i][0] = fmin(fmax(r, 0.0), 1.0);
        out[i][1] = fmin(fmax(g, 0.0), 1.0);
        out[i][2] = fmin(fmax(b, 0.0), 1.0);
    }
}

/* Blurred, enlarged copies of the artwork that drift behind everything. Each song gets
 * its own layer, so a new one fades in while the old one fades out. */
typedef struct {
    cairo_surface_t *comp_s;              /* the artwork itself, reduced to COMP_PX x COMP_PX (this reduction is the blur): exact colors, same layout */
    double           a, target;           /* opacity now / wanted */
    double           luma;                /* how bright the artwork is (0..1), for the text-readability veil */
} BgLayer;

#define COMP_PX 3                         /* 54 before, 96 before that: the blur is 21 times wider than at 54 (+2000%) */
static BgLayer bg_layers[3];
static int     bg_hidden;                 /* window minimized: no animation */

static int motion_ok(void) {              /* respects the system "reduce animations" setting */
    gboolean on = TRUE;
    g_object_get(gtk_settings_get_default(), "gtk-enable-animations", &on, NULL);
    return on;
}

static void bg_layer_free(BgLayer *l) {
    if (l->comp_s) cairo_surface_destroy(l->comp_s);
    memset(l, 0, sizeof *l);
}

/* Where the artwork sits in the window right now. It is the artwork's own layout, filling the window (a little larger
 * than the window so its edges never show) and drifting by a few percent, never rearranged: every color stays in
 * its place relative to the others. */
static double bgm_left, bgm_top, bgm_side;           /* the mapping used for the last full-size draw */

static void bg_map(double W, double H, double t, double *left, double *top, double *side) {
    const double TAU = 6.283185307179586;
    double big = fmax(W, H);
    *side = big * (1.08 + 0.02 * sin(TAU * t / 23.0));
    *left = W / 2 - *side / 2 + 0.02 * big * sin(TAU * t / 47.0);
    *top  = H / 2 - *side / 2 + 0.02 * big * cos(TAU * t / 61.0);
}

static void bg_comp(cairo_t *cr, cairo_surface_t *s, double left, double top, double side, double alpha) {
    if (!s || alpha <= 0.001) return;
    cairo_save(cr);
    cairo_translate(cr, left, top);
    cairo_scale(cr, side / COMP_PX, side / COMP_PX);
    cairo_set_source_surface(cr, s, 0, 0);
    cairo_pattern_t *p = cairo_get_source(cr);
    cairo_pattern_set_filter(p, CAIRO_FILTER_BILINEAR);
    cairo_pattern_set_extend(p, CAIRO_EXTEND_PAD);
    cairo_paint_with_alpha(cr, alpha);
    cairo_restore(cr);
}

/* The color of the blurred artwork at a window position (the newest layer), read the same way the picture is drawn
 * (bilinear between the reduced pixels), so a bubble matches exactly what is behind it: 1 = found. */
static int bg_sample(double wx, double wy, double out[3]) {
    cairo_surface_t *s = bg_layers[0].comp_s;
    if (!s || bgm_side <= 1.0) return 0;
    cairo_surface_flush(s);
    const unsigned char *d = cairo_image_surface_get_data(s);
    if (!d) return 0;
    int stride = cairo_image_surface_get_stride(s);
    int argb = cairo_image_surface_get_format(s) == CAIRO_FORMAT_ARGB32;

    double fx = (wx - bgm_left) / bgm_side * COMP_PX - 0.5, fy = (wy - bgm_top) / bgm_side * COMP_PX - 0.5;
    if (fx < 0) fx = 0;
    if (fx > COMP_PX - 1) fx = COMP_PX - 1;          /* the picture's edge colors continue outward */
    if (fy < 0) fy = 0;
    if (fy > COMP_PX - 1) fy = COMP_PX - 1;
    int x0 = (int)fx, y0 = (int)fy;
    int x1 = x0 + 1 < COMP_PX ? x0 + 1 : x0, y1 = y0 + 1 < COMP_PX ? y0 + 1 : y0;
    double tx = fx - x0, ty = fy - y0;
    out[0] = out[1] = out[2] = 0;
    for (int q = 0; q < 4; q++) {
        int x = (q & 1) ? x1 : x0, y = (q & 2) ? y1 : y0;
        double w = ((q & 1) ? tx : 1 - tx) * ((q & 2) ? ty : 1 - ty);
        const unsigned char *px = d + (size_t)y * stride + (size_t)x * 4;
        double al = argb ? px[3] / 255.0 : 1.0;
        if (al < 0.01) al = 1.0;
        out[0] += w * px[2] / 255.0 / al;  out[1] += w * px[1] / 255.0 / al;  out[2] += w * px[0] / 255.0 / al;
    }
    for (int k = 0; k < 3; k++) if (out[k] > 1.0) out[k] = 1.0;
    return 1;
}

/* ---- bubbles, soft blobs and sparkles (colors come from the artwork) ---- */

enum { FX_NEUTRAL, FX_POP, FX_HIPHOP, FX_ROCK, FX_EDM, FX_JAZZ, FX_CLASSICAL, FX_AMBIENT };

/* The genre only changes how the bubbles behave (how many, how big, how fast, how wobbly), never the mood:
 * every style is soft and floaty. */
typedef struct {
    const char *name;
    int    count;
    double speed;       /* sideways drift, screen widths per second */
    double rise;        /* screen heights per second, negative = floats up */
    double rmin, rmax;  /* bubble radius in pixels */
    double alpha;       /* bubble visibility */
    double wobble;      /* sway */
    double sparkle;     /* how many sparkles show (0..1) */
    double squish;      /* jelly wobble of the bubble shape */
    double blob;        /* strength of the big soft shapes */
} FxStyle;

static const FxStyle fx_styles[] = {
    /* name        n  speed  rise    rmin rmax alpha wob  spk  squish blob */
    {"neutral",    13, 0.010, -0.018, 14, 50, 0.90, 0.8, 0.60, 0.04, 1.0},
    {"pop",        18, 0.014, -0.026, 14, 58, 1.00, 1.0, 1.00, 0.06, 1.1},
    {"hip-hop",    12, 0.010, -0.016, 20, 68, 0.95, 0.7, 0.60, 0.05, 1.1},
    {"rock",       16, 0.016, -0.030, 12, 46, 0.95, 1.0, 0.80, 0.05, 1.0},
    {"electronic", 20, 0.018, -0.034, 12, 52, 1.00, 1.2, 1.00, 0.08, 1.0},
    {"jazz/soul",  13, 0.008, -0.014, 16, 60, 0.90, 0.9, 0.60, 0.04, 1.0},
    {"classical",  11, 0.005, -0.010, 14, 52, 0.85, 0.6, 0.90, 0.03, 0.9},
    {"ambient",    12, 0.006, -0.008, 20, 70, 0.85, 0.6, 0.50, 0.03, 1.0},
};

typedef struct { double x, y, vx, vy, r, ph; int ci; } Part;
#define FX_MAX 48
static Part   fx_parts[FX_MAX];
static int    fx_style = FX_NEUTRAL;
static double fx_a, fx_target;            /* overall visibility, fades in and out */
static double fx_kick;                    /* 1 right after a song change: the bubbles float up a little faster */

#define SP_MAX 16
static struct { double x, y, ph, sz, per; } fx_sp[SP_MAX];
static int fx_sp_ready;

/* A word must start at a word boundary; short words must also end at one,
 * so "rap" does not match "therapy" and "pop" does not match "popular". */
static int has_word(const char *hay, const char *const *words) {
    for (; *words; words++) {
        size_t wl = strlen(*words);
        for (const char *p = hay; (p = strstr(p, *words)) != NULL; p++) {
            int start_ok = p == hay || !isalnum((unsigned char)p[-1]);
            int end_ok = wl > 4 || !isalnum((unsigned char)p[wl]);
            if (start_ok && end_ok) return 1;
        }
    }
    return 0;
}

/* Genre text (or, failing that, words from the song / artist name) -> a style. */
static int fx_pick_style(const char *text) {
    char low[400];
    size_t i = 0;
    for (; text[i] && i < sizeof low - 1; i++) low[i] = (char)tolower((unsigned char)text[i]);
    low[i] = '\0';

    static const char *const hh[]  = {"hip hop", "hip-hop", "rap", "trap", "drill", NULL};
    static const char *const rk[]  = {"rock", "metal", "punk", "grunge", "hardcore", NULL};
    static const char *const ed[]  = {"edm", "electro", "house", "techno", "trance", "dubstep",
                                      "drum and bass", NULL};
    static const char *const jz[]  = {"jazz", "soul", "r&b", "blues", "funk", "bossa", NULL};
    static const char *const cl[]  = {"classical", "orchestra", "baroque", "symphon", "concerto",
                                      "opera", "piano", "sonata", NULL};
    static const char *const am[]  = {"ambient", "lo-fi", "lofi", "chill", "downtempo", "sleep",
                                      "new age", "drone", NULL};
    static const char *const pp[]  = {"pop", "k-pop", "idol", "disco", NULL};

    if (has_word(low, hh)) return FX_HIPHOP;
    if (has_word(low, rk)) return FX_ROCK;
    if (has_word(low, ed)) return FX_EDM;
    if (has_word(low, jz)) return FX_JAZZ;
    if (has_word(low, cl)) return FX_CLASSICAL;
    if (has_word(low, am)) return FX_AMBIENT;
    if (has_word(low, pp)) return FX_POP;
    return FX_NEUTRAL;
}

static double frand(void) { return g_random_double(); }

static void fx_seed(int style) {
    fx_style = style;
    const FxStyle *f = &fx_styles[style];
    for (int i = 0; i < FX_MAX; i++) {
        Part *p = &fx_parts[i];
        p->x = frand();  p->y = frand();
        p->vx = (frand() - 0.5) * 2 * f->speed;
        p->vy = f->rise * (0.5 + frand());
        /* three size classes so the bubbles are clearly different: a few large "statement" bubbles, some medium
         * ones and many tiny ones (the style's rmax scales all of them a little) */
        double k = f->rmax / 56.0;
        if (i % 6 == 0)      p->r = (50.0 + 34.0 * frand()) * fmin(k, 1.15);               /* large  */
        else if (i % 3 == 1) p->r = (20.0 + 18.0 * frand()) * k;               /* medium */
        else                 p->r = (5.0 + 9.0 * frand()) * k;                 /* tiny   */
        p->ph = frand() * 6.2832;
        p->ci = (int)(frand() * 3.0) % 3;
    }
    if (!fx_sp_ready) {
        for (int i = 0; i < SP_MAX; i++) {
            fx_sp[i].x = frand();  fx_sp[i].y = frand();
            fx_sp[i].ph = frand() * 6.2832;
            fx_sp[i].sz = 5.0 + 8.0 * frand();
            fx_sp[i].per = 2.6 + 3.4 * frand();
        }
        fx_sp_ready = 1;
    }
    fx_a = 0.0;                                       /* the new style fades in */
}

/* Soft candy version of one of the artwork's three colors: lifted and mixed with white. Artwork with hardly any
 * color (black / white / gray covers, or nothing playing) gets a gentle pink, lavender and mint instead, and the
 * change between the two is gradual because bg_cur itself fades. */
static void bg_pal(int i, double out[3]) {
    static const double dflt[3][3] = {{1.00, 0.45, 0.75}, {0.58, 0.48, 1.00}, {0.30, 0.92, 0.80}};
    const double *c = ui.bg_cur[i];
    double h, s, v;
    rgb_to_hsv(c[0], c[1], c[2], &h, &s, &v);
    double w = s * 6.0;                                             /* gray artwork -> the default candy colors */
    if (w > 1.0) w = 1.0;
    double vr, vg, vb;                                              /* the artwork's hue, pushed to vivid and bright */
    hsv_to_rgb(h, fmin(1.0, 0.62 + 0.38 * s * 1.6), 1.0, &vr, &vg, &vb);
    const double vv[3] = {vr, vg, vb};
    for (int k = 0; k < 3; k++) out[k] = vv[k] * w + dflt[i][k] * (1.0 - w);
}

static void fx_step(double dt) {
    const FxStyle *f = &fx_styles[fx_style];
    double sp = ui.playing ? 1.0 : 0.30;              /* paused: drifting very slowly */
    double t = g_get_monotonic_time() / 1e6;
    double lift = 1.0 + 2.2 * fx_kick;
    fx_kick *= exp(-dt / 1.1);
    if (fx_kick < 0.01) fx_kick = 0;

    for (int i = 0; i < f->count; i++) {
        Part *p = &fx_parts[i];
        p->x += (p->vx + f->wobble * 0.014 * sin(t * 0.5 + p->ph)) * dt * sp;
        p->y += p->vy * lift * dt * sp;
        if (p->x < -0.06) p->x += 1.12;
        if (p->x > 1.06)  p->x -= 1.12;
        if (p->y < -0.10) { p->y = 1.10; p->x = frand(); }
        if (p->y > 1.10)  { p->y = -0.10; p->x = frand(); }
    }
    for (int i = 0; i < SP_MAX; i++) {                 /* sparkles just drift a little */
        fx_sp[i].y += -0.004 * dt * sp;
        fx_sp[i].x += 0.003 * sin(t * 0.3 + fx_sp[i].ph) * dt * sp;
        if (fx_sp[i].y < -0.05) { fx_sp[i].y = 1.05; fx_sp[i].x = frand(); }
    }
}

/* A big, slow, organic shape (a rounded blob whose outline breathes).
 * Precomputed: the angle tables below are built once; per frame only the three phase terms are computed (angle-addition
 * formula), instead of ~120 sin() calls per blob. */
#define BLOB_N 40
static double bl_c1[BLOB_N + 1], bl_s1[BLOB_N + 1];
static double bl_c2[BLOB_N + 1], bl_s2[BLOB_N + 1];
static double bl_c3[BLOB_N + 1], bl_s3[BLOB_N + 1];
static double bl_c5[BLOB_N + 1], bl_s5[BLOB_N + 1];
static int    bl_ready;

static void blob_tables(void) {
    for (int i = 0; i <= BLOB_N; i++) {
        double th = 6.283185307179586 * i / BLOB_N;
        bl_c1[i] = cos(th);      bl_s1[i] = sin(th);
        bl_c2[i] = cos(2 * th);  bl_s2[i] = sin(2 * th);
        bl_c3[i] = cos(3 * th);  bl_s3[i] = sin(3 * th);
        bl_c5[i] = cos(5 * th);  bl_s5[i] = sin(5 * th);
    }
    bl_ready = 1;
}

static void fx_blob(cairo_t *cr, double cx, double cy, double R, double t, double seed, const double c[3], double a) {
    if (!bl_ready) blob_tables();
    double p2 = t / 9.0 + seed, p3 = -t / 7.0 + seed * 2.0, p5 = t / 5.0 + seed * 3.0;
    double s2 = sin(p2), c2 = cos(p2), s3 = sin(p3), c3 = cos(p3), s5 = sin(p5), c5 = cos(p5);
    cairo_new_path(cr);
    for (int i = 0; i <= BLOB_N; i++) {
        double r = R * (1.0 + 0.13 * (bl_s2[i] * c2 + bl_c2[i] * s2) + 0.08 * (bl_s3[i] * c3 + bl_c3[i] * s3)
                            + 0.04 * (bl_s5[i] * c5 + bl_c5[i] * s5));
        double x = cx + bl_c1[i] * r, y = cy + bl_s1[i] * r;
        if (i == 0) cairo_move_to(cr, x, y); else cairo_line_to(cr, x, y);
    }
    cairo_close_path(cr);
    cairo_pattern_t *g = cairo_pattern_create_radial(cx, cy, 0, cx, cy, R * 0.92);          /* fades to nothing inside the outline: no hard edge */
    cairo_pattern_add_color_stop_rgba(g, 0.0, c[0], c[1], c[2], a);
    cairo_pattern_add_color_stop_rgba(g, 0.55, c[0], c[1], c[2], a * 0.45);
    cairo_pattern_add_color_stop_rgba(g, 1.0, c[0], c[1], c[2], 0.0);
    cairo_set_source(cr, g);
    cairo_fill(cr);
    cairo_pattern_destroy(g);
}

/* A soap bubble with the rainbow sheen of a real one: clear in the middle, color toward the edge, the color drifting
 * across the bubble from one side to the other, a bright thin rim, a soft glossy spot and a small glint. The sheen
 * colors are the song's color turned around the color wheel (so they always belong to the background, never a fixed
 * rainbow). */
static void fx_sheen_colors(const double c[3], double ic[4][3]) {
    double h, s, v;
    rgb_to_hsv(c[0], c[1], c[2], &h, &s, &v);
    static const double turn[4] = {-55.0, -15.0, 30.0, 85.0};
    for (int i = 0; i < 4; i++)
        hsv_to_rgb(fmod(h + turn[i] + 720.0, 360.0), 0.50, 1.0, &ic[i][0], &ic[i][1], &ic[i][2]);
}

/* The bubble takes its colors from the background right where it floats: four exact colors read from the artwork along
 * the diagonal through the bubble (inside it, so a bubble over two color regions shows both). The side facing the light
 * is that same color a little lighter, the far side a little deeper, which gives the glassy depth without any new hue.
 * (Without artwork the soft default colors are used instead.) */
static void fx_bubble_colors(double x, double y, double r, const double fallback[4][3], double ic[4][3]) {
    static const double d[4]    = {-1.0, -0.35, 0.35, 1.0};
    static const double lite[4] = {0.38, 0.20, 0.0, 0.0};      /* mix toward white */
    static const double dark[4] = {1.0, 1.0, 0.92, 0.80};      /* brightness */
    for (int i = 0; i < 4; i++) {
        double o = d[i] * r * 0.75;
        if (!bg_sample(x + o, y + o, ic[i])) memcpy(ic[i], fallback[i], sizeof ic[i]);
        for (int k = 0; k < 3; k++) ic[i][k] = (ic[i][k] + (1.0 - ic[i][k]) * lite[i]) * dark[i];
    }
}

static void fx_bubble(cairo_t *cr, double x, double y, double r, double squish, const double ic[4][3], double a) {
    const double TAU = 6.283185307179586;

    cairo_save(cr);
    cairo_translate(cr, x, y);
    cairo_scale(cr, 1.0 + squish, 1.0 - squish);

    /* body: the sheen, faded out toward the middle with a mask */
    cairo_pattern_t *sheen = cairo_pattern_create_linear(-r * 0.8, -r * 0.8, r * 0.8, r * 0.8);
    cairo_pattern_add_color_stop_rgba(sheen, 0.00, ic[0][0], ic[0][1], ic[0][2], 0.85);
    cairo_pattern_add_color_stop_rgba(sheen, 0.38, ic[1][0], ic[1][1], ic[1][2], 0.55);
    cairo_pattern_add_color_stop_rgba(sheen, 0.68, ic[2][0], ic[2][1], ic[2][2], 0.70);
    cairo_pattern_add_color_stop_rgba(sheen, 1.00, ic[3][0], ic[3][1], ic[3][2], 0.90);
    cairo_pattern_t *fade = cairo_pattern_create_radial(0, 0, 0, 0, 0, r);
    cairo_pattern_add_color_stop_rgba(fade, 0.0, 0, 0, 0, a * 0.10);
    cairo_pattern_add_color_stop_rgba(fade, 0.55, 0, 0, 0, a * 0.22);
    cairo_pattern_add_color_stop_rgba(fade, 0.90, 0, 0, 0, a * 0.62);
    cairo_pattern_add_color_stop_rgba(fade, 1.0, 0, 0, 0, a * 0.72);
    cairo_arc(cr, 0, 0, r, 0, TAU);
    cairo_clip(cr);
    cairo_set_source(cr, sheen);
    cairo_mask(cr, fade);
    cairo_reset_clip(cr);
    cairo_pattern_destroy(fade);
    cairo_pattern_destroy(sheen);

    /* rim: a thin ring in the opposite sheen direction, plus a fine white edge */
    cairo_pattern_t *rim = cairo_pattern_create_linear(r * 0.8, -r * 0.8, -r * 0.8, r * 0.8);
    cairo_pattern_add_color_stop_rgba(rim, 0.0, ic[2][0], ic[2][1], ic[2][2], a * 0.75);
    cairo_pattern_add_color_stop_rgba(rim, 0.5, 1.0, 1.0, 1.0, a * 0.55);
    cairo_pattern_add_color_stop_rgba(rim, 1.0, ic[0][0], ic[0][1], ic[0][2], a * 0.75);
    cairo_arc(cr, 0, 0, r * 0.97, 0, TAU);
    cairo_set_source(cr, rim);
    cairo_set_line_width(cr, fmax(1.2, r * 0.07));
    cairo_stroke(cr);
    cairo_pattern_destroy(rim);
    cairo_arc(cr, 0, 0, r, 0, TAU);
    cairo_set_source_rgba(cr, 1, 1, 1, a * 0.40);
    cairo_set_line_width(cr, fmax(0.8, r * 0.025));
    cairo_stroke(cr);

    /* glossy spot (soft) with a crisp core, top left */
    cairo_pattern_t *g = cairo_pattern_create_radial(-r * 0.42, -r * 0.44, 0, -r * 0.42, -r * 0.44, r * 0.34);
    cairo_pattern_add_color_stop_rgba(g, 0.0, 1, 1, 1, a * 0.85);
    cairo_pattern_add_color_stop_rgba(g, 0.45, 1, 1, 1, a * 0.30);
    cairo_pattern_add_color_stop_rgba(g, 1.0, 1, 1, 1, 0.0);
    cairo_set_source(cr, g);
    cairo_arc(cr, -r * 0.42, -r * 0.44, r * 0.34, 0, TAU);
    cairo_fill(cr);
    cairo_pattern_destroy(g);

    cairo_save(cr);
    cairo_translate(cr, -r * 0.40, -r * 0.44);
    cairo_rotate(cr, -0.7);
    cairo_scale(cr, r * 0.15, r * 0.07);
    cairo_arc(cr, 0, 0, 1.0, 0, TAU);
    cairo_restore(cr);
    cairo_set_source_rgba(cr, 1, 1, 1, a * 0.9);
    cairo_fill(cr);

    /* glint along the lower right edge */
    cairo_arc(cr, 0, 0, r * 0.84, 0.35, 1.05);
    cairo_set_source_rgba(cr, 1, 1, 1, a * 0.42);
    cairo_set_line_width(cr, fmax(1.0, r * 0.05));
    cairo_set_line_cap(cr, CAIRO_LINE_CAP_ROUND);
    cairo_stroke(cr);
    cairo_restore(cr);
}

/* A little four-point sparkle with a soft halo. */
static void fx_sparkle(cairo_t *cr, double x, double y, double s, double a) {
    cairo_pattern_t *g = cairo_pattern_create_radial(x, y, 0, x, y, s * 1.8);
    cairo_pattern_add_color_stop_rgba(g, 0.0, 1, 1, 1, a * 0.45);
    cairo_pattern_add_color_stop_rgba(g, 1.0, 1, 1, 1, 0.0);
    cairo_set_source(cr, g);
    cairo_arc(cr, x, y, s * 1.8, 0, 6.283185307179586);
    cairo_fill(cr);
    cairo_pattern_destroy(g);

    double k = s * 0.14;
    cairo_new_path(cr);
    cairo_move_to(cr, x, y - s);
    cairo_curve_to(cr, x + k, y - k, x + k, y - k, x + s, y);
    cairo_curve_to(cr, x + k, y + k, x + k, y + k, x, y + s);
    cairo_curve_to(cr, x - k, y + k, x - k, y + k, x - s, y);
    cairo_curve_to(cr, x - k, y - k, x - k, y - k, x, y - s);
    cairo_close_path(cr);
    cairo_set_source_rgba(cr, 1, 1, 1, a);
    cairo_fill(cr);
}

/* The big soft shapes belong to the blurred layer (drawn at reduced size, see bg_draw). */
static void fx_blobs(cairo_t *cr, double W, double H, double t) {
    const double TAU = 6.283185307179586;
    const FxStyle *f = &fx_styles[fx_style];
    double big = fmax(W, H);
    static const double white[3] = {1.0, 1.0, 1.0};      /* light only: no color is added to the artwork's colors */
    /* --- three big soft organic shapes drifting slowly (replace the old light rays) --- */
    static const double bx[3] = {0.22, 0.80, 0.52}, by[3] = {0.28, 0.40, 0.88};
    for (int i = 0; i < 3; i++) {
        double cx = (bx[i] + 0.07 * sin(TAU * t / (53.0 + 11 * i) + i * 2.0)) * W;
        double cy = (by[i] + 0.06 * cos(TAU * t / (67.0 + 9 * i) + i)) * H;
        fx_blob(cr, cx, cy, big * (0.26 + 0.03 * i), t, i * 1.9, white, fx_a * f->blob * 0.12);
    }

}

static void fx_draw(cairo_t *cr, double W, double H, double t) {
    const double TAU = 6.283185307179586;
    const FxStyle *f = &fx_styles[fx_style];
    double pal[3][3];
    for (int i = 0; i < 3; i++) bg_pal(i, pal[i]);

    /* --- bubbles: normal blending, so the glossy rims stay light --- */
    cairo_set_operator(cr, CAIRO_OPERATOR_OVER);
    double sheen[3][4][3];                                   /* computed once per frame, not once per bubble */
    for (int i = 0; i < 3; i++) fx_sheen_colors(pal[i], sheen[i]);
    double cx1, cy1, cx2, cy2;                               /* the part of the window being repainted */
    cairo_clip_extents(cr, &cx1, &cy1, &cx2, &cy2);
    for (int i = 0; i < f->count; i++) {
        const Part *p = &fx_parts[i];
        double bx = p->x * W, by = p->y * H, m = p->r * 1.25;
        if (bx + m < cx1 || bx - m > cx2 || by + m < cy1 || by - m > cy2) continue;      /* outside: not drawn */
        double sq = f->squish * sin(TAU * t / (3.2 + p->ph * 0.4) + p->ph);
        double a = fx_a * f->alpha * (0.70 + 0.30 * fmin(1.0, p->r / 60.0));
        double ic[4][3];
        fx_bubble_colors(bx, by, p->r, sheen[p->ci], ic);
        fx_bubble(cr, bx, by, p->r, sq, ic, a > 1.0 ? 1.0 : a);
    }

    /* --- sparkles --- */
    int nsp = (int)(SP_MAX * f->sparkle + 0.5);
    if (nsp > SP_MAX) nsp = SP_MAX;
    for (int i = 0; i < nsp; i++) {
        double ph = 0.5 + 0.5 * sin(TAU * t / fx_sp[i].per + fx_sp[i].ph);
        double tw = ph * ph * ph;                                     /* mostly dim, brief shine */
        if (tw < 0.03) continue;
        fx_sparkle(cr, fx_sp[i].x * W, fx_sp[i].y * H, fx_sp[i].sz * (0.6 + 0.4 * tw), fx_a * 0.85 * tw);
    }
    cairo_set_operator(cr, CAIRO_OPERATOR_SCREEN);
}

/* Everything that is soft: gradient, blurred artwork, glows, sheen, big shapes. */
#define LO_DIV 4                  /* the soft layer is drawn at 1/4 of the width and height (1/16 of the pixels) */
#define LO_EVERY_US 66000         /* ... and at most about 15 times a second */

static void bg_soft(cairo_t *cr, double W, double H, double t) {
    const double TAU = 6.283185307179586;

    /* Only used before any artwork is there (and while the very first one fades in): the soft default colors. */
    {
        static const double dc[3][3] = {{1.00, 0.45, 0.75}, {0.58, 0.48, 1.00}, {0.30, 0.92, 0.80}};
        double sh = 0.06 * sin(TAU * t / 41.0);
        cairo_pattern_t *g = cairo_pattern_create_linear(0, 0, W * (0.6 + sh), H);
        cairo_pattern_add_color_stop_rgb(g, 0.0, dc[0][0] * 0.66, dc[0][1] * 0.66, dc[0][2] * 0.66);
        cairo_pattern_add_color_stop_rgb(g, 0.50, dc[2][0] * 0.56, dc[2][1] * 0.56, dc[2][2] * 0.56);
        cairo_pattern_add_color_stop_rgb(g, 1.0, dc[1][0] * 0.64, dc[1][1] * 0.64, dc[1][2] * 0.64);
        cairo_set_source(cr, g);
        cairo_paint(cr);
        cairo_pattern_destroy(g);
    }

    /* The artwork's own colors, in the artwork's own layout: drawn as is (only reduced in size, which softens the
     * borders between color regions a little), no averaging, no extra colors. The older song stays fully visible until
     * the new one has faded in over it. */
    double left, top, side;
    bg_map(W, H, t, &left, &top, &side);
    int any = 0;
    for (int i = 2; i >= 0; i--) {                            /* oldest first */
        const BgLayer *l = &bg_layers[i];
        if (!l->comp_s) continue;
        any = 1;
        bg_comp(cr, l->comp_s, left, top, side, l->a);
    }
    if (any) {
        /* The text is white, so a bright cover needs a darker veil (black, no new hue) and a dark one hardly any: the
         * veil is chosen so the artwork ends up at about half brightness at most, which keeps white text readable. */
        double lum = 0.5;
        for (int i = 2; i >= 0; i--)
            if (bg_layers[i].comp_s) lum = lum * (1.0 - bg_layers[i].a) + bg_layers[i].luma * bg_layers[i].a;
        double va = lum > 0.50 ? 1.0 - 0.50 / lum : 0.0;
        if (va < 0.10) va = 0.10;
        if (va > 0.55) va = 0.55;
        cairo_set_source_rgba(cr, 0.0, 0.0, 0.0, va);
        cairo_paint(cr);
    }

    cairo_set_operator(cr, CAIRO_OPERATOR_OVER);              /* glossy sheen: light from the top that fades out */
    {
        cairo_pattern_t *g = cairo_pattern_create_linear(0, 0, 0, H * 0.55);
        cairo_pattern_add_color_stop_rgba(g, 0.0, 1, 1, 1, 0.14);
        cairo_pattern_add_color_stop_rgba(g, 1.0, 1, 1, 1, 0.0);
        cairo_set_source(cr, g);
        cairo_rectangle(cr, 0, 0, W, H * 0.55);
        cairo_fill(cr);
        cairo_pattern_destroy(g);
    }
    cairo_set_operator(cr, CAIRO_OPERATOR_SCREEN);
    if (fx_a > 0.002) fx_blobs(cr, W, H, t);
    cairo_set_operator(cr, CAIRO_OPERATOR_OVER);
}

/* Optimization: the soft part has no sharp detail, so it is drawn at 1/16 of the pixels (a quarter of the width and
 * height) and at most about 15 times a second (it drifts over tens of seconds), then scaled up smoothly. That is where
 * most of the time went (full-window gradients and blends). The sharp bubbles and sparkles are drawn every frame at
 * full size on top. */
static gboolean bg_draw(GtkWidget *w, cairo_t *cr, gpointer unused) {
    double W = gtk_widget_get_allocated_width(w), H = gtk_widget_get_allocated_height(w);
    if (W < 2 || H < 2) return FALSE;
    double t = motion_ok() ? g_get_monotonic_time() / 1e6 : 0.0;
    bg_map(W, H, t, &bgm_left, &bgm_top, &bgm_side);      /* the bubbles read the artwork's colors at this mapping */
    static cairo_surface_t *lo;
    static cairo_t *lc;                                    /* kept between frames: no create / destroy every time */
    static int lo_w, lo_h;
    static gint64 lo_last_us;
    int lw = (int)(W / LO_DIV) + 1, lh = (int)(H / LO_DIV) + 1;

    if (!lo || lw != lo_w || lh != lo_h) {
        if (lc) cairo_destroy(lc);
        if (lo) cairo_surface_destroy(lo);
        lo = cairo_image_surface_create(CAIRO_FORMAT_RGB24, lw, lh);
        lc = cairo_create(lo);
        lo_w = lw;  lo_h = lh;
        lo_last_us = 0;                                    /* new size: draw it now */
    }
    gint64 now_us = g_get_monotonic_time();
    if (!lo_last_us || now_us - lo_last_us >= LO_EVERY_US) {     /* by elapsed time, not by frame count */
        lo_last_us = now_us;
        cairo_save(lc);
        cairo_scale(lc, (double)lw / W, (double)lh / H);
        bg_soft(lc, W, H, t);
        cairo_restore(lc);
    }

    cairo_save(cr);
    cairo_scale(cr, W / lw, H / lh);
    cairo_set_source_surface(cr, lo, 0, 0);
    cairo_pattern_set_filter(cairo_get_source(cr), CAIRO_FILTER_BILINEAR);
    cairo_pattern_set_extend(cairo_get_source(cr), CAIRO_EXTEND_PAD);      /* no dark line at the window edge */
    cairo_set_operator(cr, CAIRO_OPERATOR_SOURCE);
    cairo_paint(cr);
    cairo_restore(cr);

    cairo_set_operator(cr, CAIRO_OPERATOR_OVER);
    if (fx_a > 0.002) fx_draw(cr, W, H, t);
    cairo_set_operator(cr, CAIRO_OPERATOR_OVER);
    return FALSE;
}

/* One lightweight timer (about 30 fps) drives color fades, artwork fades and the drift.
 * It stops by itself when nothing moves, when the window is minimized, or when the
 * system asks for reduced motion and the fades are done. */
/* The animation step runs on the widget's frame clock (a GTK "tick callback"): GTK paces it with the display's refresh
 * (the vertical-sync of this backend) and stops it by itself while the window is not shown, so there are no timers
 * and no wake-ups for frames nobody sees. On top of that:
 *   - frame limit: at most ~30 steps a second (about 15 while the window is not the active one, or paused);
 *   - delta time: every fade and movement is "rate x elapsed seconds", so the speed is the same at any frame rate;
 *   - nothing is scheduled at all once everything has settled (it restarts from bg_wake()).
 * GTK double-buffers the window (it paints into an off-screen surface and presents it whole), so there is no flicker. */
#define BG_FRAME_US        33333      /* 30 fps while playing in the active window */
#define BG_FRAME_SLOW_US   66666      /* 15 fps: paused, or the window is in the background */

static gboolean bg_frame(GtkWidget *w, GdkFrameClock *fc, gpointer unused) {
    if (bg_hidden || g_atomic_int_get(&app_closing)) { ui.bg_timer = 0; return G_SOURCE_REMOVE; }

    static gint64 last_us;
    gint64 now = gdk_frame_clock_get_frame_time(fc);
    int active = ui.win && gtk_window_is_active(GTK_WINDOW(ui.win));
    gint64 gap = (ui.playing && active) ? BG_FRAME_US : BG_FRAME_SLOW_US;
    if (last_us && now - last_us < gap - 4000) return G_SOURCE_CONTINUE;       /* over the limit: skip this display frame */
    double dt = last_us ? (double)(now - last_us) / 1e6 : 1.0 / 30.0;
    last_us = now;
    if (dt > 0.2) dt = 0.2;

    int calm = !motion_ok();
    int moving = 0, shown = 0;

    /* rates per second, equal to the old per-33-ms steps: colors 9% per step, art 0.035 per step, effects 0.02 / 0.03 */
    double k_col = 1.0 - exp(-2.86 * dt);
    for (int i = 0; i < 3; i++)
        for (int k = 0; k < 3; k++) {
            double d = ui.bg_tgt[i][k] - ui.bg_cur[i][k];
            if (calm || fabs(d) < 0.003) ui.bg_cur[i][k] = ui.bg_tgt[i][k];
            else { ui.bg_cur[i][k] += d * k_col; moving = 1; }
        }

    int newest_in = bg_layers[0].comp_s && bg_layers[0].target == 1.0;   /* a new song is fading in over the old one */
    for (int i = 0; i < 3; i++) {
        BgLayer *l = &bg_layers[i];
        if (!l->comp_s) continue;
        if (i > 0 && newest_in) {                                           /* the old song stays until the new one is in */
            if (bg_layers[0].a >= 0.999) bg_layer_free(l);
            else { shown = 1; moving = 1; }
            continue;
        }
        double d = l->target - l->a, step = 1.06 * dt;                      /* about 1 s cross-fade */
        if (calm || fabs(d) < 0.01) l->a = l->target;
        else { l->a += d > 0 ? step : -step; moving = 1; }
        if (l->target == 0.0 && l->a == 0.0) bg_layer_free(l);
        else shown = 1;
    }

    double fd = fx_target - fx_a;                                /* effects fade in / out */
    if (calm || fabs(fd) < 0.01) fx_a = fx_target;
    else { fx_a += (fd > 0 ? 0.6 : -0.9) * dt; moving = 1; }
    if (fx_a > 1.0) fx_a = 1.0;
    if (fx_a < 0.0) fx_a = 0.0;
    int fx_on = fx_a > 0.002;
    if (fx_on && !calm) fx_step(dt);

    gtk_widget_queue_draw(w);
    if (!moving && !(shown && !calm) && !(fx_on && !calm)) {
        ui.bg_timer = 0;
        last_us = 0;
        return G_SOURCE_REMOVE;
    }
    return G_SOURCE_CONTINUE;
}

static void bg_wake(void) {
    if (!ui.bg_timer && !bg_hidden && ui.bg) ui.bg_timer = gtk_widget_add_tick_callback(ui.bg, bg_frame, NULL, NULL);
    else if (!ui.bg_timer && ui.bg) gtk_widget_queue_draw(ui.bg);
}

static void bg_set_target(double t[3][3]) {
    memcpy(ui.bg_tgt, t, sizeof ui.bg_tgt);
    fx_kick = 1.0;                                            /* bubbles float up a little on a song change */
    bg_wake();
}

static gboolean on_win_state(GtkWidget *w, GdkEventWindowState *ev, gpointer unused) {
    if (ev->changed_mask & (GDK_WINDOW_STATE_ICONIFIED | GDK_WINDOW_STATE_WITHDRAWN)) {
        int gone = (ev->new_window_state & (GDK_WINDOW_STATE_ICONIFIED | GDK_WINDOW_STATE_WITHDRAWN)) != 0;
        int was = poll_win_gone;
        poll_win_gone = gone;
        if (was && !gone) poll_wake();                        /* back on screen: poll now, normal rate */
        else if (gone && !was) poll_resched();                /* gone: slow down */
    }
    if (ev->changed_mask & GDK_WINDOW_STATE_ICONIFIED) {
        bg_hidden = (ev->new_window_state & GDK_WINDOW_STATE_ICONIFIED) != 0;
        if (!bg_hidden) bg_wake();                            /* back on screen: resume */
    }
    return FALSE;
}

static gboolean on_focus_in(GtkWidget *w, GdkEventFocus *ev, gpointer unused) {
    (void)w; (void)ev; (void)unused;
    if (ui.logged_in) poll_wake();            /* looking at the window again: show the real state at once */
    return FALSE;
}

static void bg_to_default(void) {
    double t[3][3];
    for (int i = 0; i < 3; i++) t[i][0] = t[i][1] = t[i][2] = BG_BASE;
    ui.bg_set[0] = '\0';
    for (int i = 0; i < 3; i++) bg_layers[i].target = 0.0;    /* artwork fades out */
    bg_set_target(t);
}

/* A new artwork layer: the older ones fade out, this one fades in. */
static void bg_push_layer(GdkPixbuf *pb) {
    GdkPixbuf *f = gdk_pixbuf_scale_simple(pb, COMP_PX, COMP_PX, GDK_INTERP_HYPER);   /* area-accurate reduction */
    if (!f) return;

    bg_layer_free(&bg_layers[2]);                              /* rapid changes: drop the oldest */
    bg_layers[2] = bg_layers[1];
    bg_layers[1] = bg_layers[0];
    memset(&bg_layers[0], 0, sizeof bg_layers[0]);
    bg_layers[0].comp_s = gdk_cairo_surface_create_from_pixbuf(f, 1, NULL);
    {                                                          /* brightness: half the average, half the brightest spot */
        cairo_surface_t *s = bg_layers[0].comp_s;
        const unsigned char *d = cairo_image_surface_get_data(s);
        int st = cairo_image_surface_get_stride(s), argb = cairo_image_surface_get_format(s) == CAIRO_FORMAT_ARGB32;
        double sum = 0, mx = 0;
        for (int y = 0; d && y < COMP_PX; y++)
            for (int x = 0; x < COMP_PX; x++) {
                const unsigned char *p = d + (size_t)y * st + (size_t)x * 4;
                double al = argb && p[3] ? p[3] / 255.0 : 1.0;
                double Y = (0.2126 * p[2] + 0.7152 * p[1] + 0.0722 * p[0]) / 255.0 / al;
                if (Y > 1.0) Y = 1.0;
                sum += Y;  if (Y > mx) mx = Y;
            }
        bg_layers[0].luma = 0.5 * sum / (COMP_PX * COMP_PX) + 0.5 * mx;
    }
    bg_layers[0].a = 0.0;
    bg_layers[0].target = 1.0;
    for (int i = 1; i < 3; i++) bg_layers[i].target = 0.0;
    g_object_unref(f);
}

/* Called with every playback update and when a picture arrives. The colors and the
 * artwork always come from the song that is playing right now. */
static void bg_update(void) {
    if (!ui.bg) return;

    if (!ui.np_img_url[0]) {                                  /* no artwork: default look */
        ui.bg_want[0] = '\0';
        if (ui.bg_set[0]) bg_to_default();
        return;
    }

    if (strcmp(ui.bg_want, ui.np_img_url) != 0) {             /* a different song started */
        snprintf(ui.bg_want, sizeof ui.bg_want, "%s", ui.np_img_url);
        if (strcmp(ui.bg_set, ui.np_img_url) != 0)
            bg_to_default();               /* never keep the last song's look while this one loads */
    }
    if (strcmp(ui.bg_set, ui.np_img_url) == 0) return;        /* already matches this song */

    GdkPixbuf *pb = art_lookup(ui.np_img_url);
    if (!pb) return;                                          /* arrives later (or failed: default) */

    double t[3][3];
    bg_extract(pb, t);
    bg_push_layer(pb);
    snprintf(ui.bg_set, sizeof ui.bg_set, "%s", ui.np_img_url);
    bg_set_target(t);
}

/* Looks up the genre of the playing artist; until then (or if Spotify lists none)
 * the style is guessed from words in the song and artist names. */
typedef struct { char artist_id[64]; char genres[300]; long status; } GenreRes;

static gboolean genre_done(gpointer data) {
    GenreRes *g = data;
    if (strcmp(g->artist_id, ui.np_artist_id) == 0 && g->status == 200 && g->genres[0]) {
        int st = fx_pick_style(g->genres);
        if (st != fx_style) fx_seed(st);
        fprintf(stderr, "[fx] genres: %s -> %s\n", g->genres, fx_styles[fx_style].name);
    }
    g_free(g);
    return G_SOURCE_REMOVE;
}

static gpointer genre_thread(gpointer data) {
    GenreRes *g = data;
    g->status = player_get_artist_genres(g->artist_id, g->genres, sizeof g->genres);
    g_idle_add(genre_done, g);
    return NULL;
}

static void fx_track(void) {
    if (!ui.bg) return;

    fx_target = ui.np_uri[0] ? 1.0 : 0.0;
    if (ui.np_uri[0] && strcmp(ui.fx_artist, ui.np_artist_id) != 0) {   /* a different artist */
        snprintf(ui.fx_artist, sizeof ui.fx_artist, "%s", ui.np_artist_id);

        char words[600];
        snprintf(words, sizeof words, "%s %s", ui.np_name, ui.np_artist_s);
        int st = fx_pick_style(words);                                  /* quick guess first */
        if (st != fx_style) fx_seed(st);

        if (ui.np_artist_id[0]) {
            GenreRes *g = g_new0(GenreRes, 1);
            snprintf(g->artist_id, sizeof g->artist_id, "%s", ui.np_artist_id);
            GThread *t = g_thread_new("genre", genre_thread, g);
            g_thread_unref(t);
        }
    }
    bg_wake();
}

/* ---------- playlist list: slide away / back ---------- */

/* Who gets the spare room: in the stacked layout the list (or the cover when the list is folded
   away); in the side-by-side layout both halves. */
static void update_pane_packing(void) {
    if (!ui.pane_top || !ui.pane_bot) return;
    int wide   = ui.lay_wide > 0;
    int folded = ui.list_folded;

    gtk_box_set_child_packing(GTK_BOX(ui.main_box), ui.pane_top,
                              wide || folded, wide || folded, 0, GTK_PACK_START);
    gtk_box_set_child_packing(GTK_BOX(ui.main_box), ui.pane_bot,
                              wide || !folded, wide || !folded, 0, GTK_PACK_START);
    gtk_box_set_child_packing(GTK_BOX(ui.pane_bot), ui.list_rev, !folded, !folded, 0, GTK_PACK_START);
    gtk_box_set_child_packing(GTK_BOX(ui.pane_top), ui.car, folded, FALSE, 0, GTK_PACK_START);
}

static void update_hint_visibility(void) {
    if (!ui.hint) return;
    int show = ui.hint_force || (ui.lay_tier == 0 && ui.lay_wide <= 0);
    gtk_widget_set_visible(ui.hint, show);
}

/* Responsive layout. Wide windows (e.g. a quarter or half of the screen in landscape) put the
   player and the list side by side; stacked otherwise. Smaller heights shrink the spacing and the
   cover row a little and let the extras (shortcut help, separator, label) give way first - nothing
   is removed, and the shortcut help comes back with H. The limits have a margin so the layout
   does not flip back and forth while you drag the window edge. */
static void apply_layout(int w, int h) {
    int was_wide = ui.lay_wide > 0;
    /* side by side for wide-and-short windows (quarter / half screen); a big window keeps the stacked look */
    int wide = was_wide ? (w >= 860 && w * 10 >= h * 13 && (w < 1550 || h < 740))
                        : (w >= 900 && w * 10 >= h * 14 && (w < 1500 || h < 700));

    int t = ui.lay_tier;
    if (t < 0)                       t = h >= 820 ? 0 : h >= 620 ? 1 : 2;
    else if (t == 0 && h < 790)      t = h >= 620 ? 1 : 2;
    else if (t == 1 && h >= 850)     t = 0;
    else if (t == 1 && h < 590)      t = 2;
    else if (t == 2 && h >= 650)     t = h >= 850 ? 0 : 1;

    if (wide == ui.lay_wide && t == ui.lay_tier) return;
    ui.lay_wide = wide;
    ui.lay_tier = t;

    static const int    car_h[3]  = { CAR_H, 204, 180 };
    static const double car_sc[3] = { 1.0, 0.88, 0.78 };
    static const int    gap[3]    = { 8, 6, 4 };
    static const int    pad[3]    = { 16, 12, 8 };

    gtk_orientable_set_orientation(GTK_ORIENTABLE(ui.main_box),
                                   wide ? GTK_ORIENTATION_HORIZONTAL : GTK_ORIENTATION_VERTICAL);
    gtk_box_set_homogeneous(GTK_BOX(ui.main_box), wide);
    gtk_box_set_spacing(GTK_BOX(ui.main_box), wide ? 16 : gap[t]);
    gtk_box_set_spacing(GTK_BOX(ui.pane_top), gap[t]);
    gtk_box_set_spacing(GTK_BOX(ui.pane_bot), gap[t]);
    gtk_container_set_border_width(GTK_CONTAINER(ui.main_box), pad[t]);

    gtk_widget_set_size_request(ui.car, -1, car_h[t]);
    car_scale = car_sc[t];

    gtk_widget_set_visible(ui.sep, t == 0 && !wide);
    gtk_widget_set_visible(ui.mini_label, t == 0);
    update_hint_visibility();
    update_pane_packing();

    GtkStyleContext *sc = gtk_widget_get_style_context(ui.win);
    gtk_style_context_remove_class(sc, "compact");
    if (t > 0) gtk_style_context_add_class(sc, "compact");

    gtk_widget_queue_draw(ui.car);
}

static void on_win_size(GtkWidget *w, GdkRectangle *a, gpointer unused) {
    apply_layout(a->width, a->height);
}

static void on_list_revealed(GObject *o, GParamSpec *p, gpointer unused) {
    if (!ui.list_open && !gtk_revealer_get_child_revealed(GTK_REVEALER(ui.list_rev))) {
        ui.list_folded = 1;                  /* fully folded: free space goes to the cover (centered) */
        update_pane_packing();
    }
}

static void set_list_open(int open) {
    if (!ui.list_rev || open == ui.list_open) return;
    ui.list_open = open;
    activity_log(ACT_SUCCESS, open ? "OPEN_PANEL" : "CLOSE_PANEL", -1, NULL, "Panel: Playlist list");
    gtk_button_set_label(GTK_BUTTON(ui.list_btn), open ? "Hide list" : "Show list");

    if (open) {
        ui.list_folded = 0;
        update_pane_packing();
    }
    gtk_revealer_set_reveal_child(GTK_REVEALER(ui.list_rev), open);
}

static void on_list_btn(GtkButton *b, gpointer unused) {
    set_list_open(!ui.list_open);
}

/* ---------- floating mini player (+ opens, - closes) ---------- */

static guint mini_fade_id;
static void mini_spin_sync(void);

static gboolean mini_fade_cb(gpointer unused) {
    double o = gtk_widget_get_opacity(ui.mini_win);
    double target = ui.mini_state == 1 ? 1.0 : 0.0;
    o += (target > o ? 1 : -1) * 0.14;                         /* about 150 ms */
    if ((target > o ? 1 : -1) != (target > gtk_widget_get_opacity(ui.mini_win) ? 1 : -1) ||
        fabs(target - o) < 0.001) o = target;
    gtk_widget_set_opacity(ui.mini_win, o);

    if (o == target) {
        mini_fade_id = 0;
        if (target == 0.0) {                                   /* fully faded out: hide it */
            gtk_widget_hide(ui.mini_win);
            poll_resched();                                    /* a hidden main window may now poll slowly */
            ui.mini_state = 0;
            mini_spin_sync();                                  /* hidden: nothing to turn */
        }
        return G_SOURCE_REMOVE;
    }
    return G_SOURCE_CONTINUE;
}

static void mini_set_buttons(void) {
    if (!ui.mini_plus) return;
    GtkStyleContext *sc = gtk_widget_get_style_context(ui.mini_plus);
    if (ui.mini_state == 1) gtk_style_context_add_class(sc, "on");
    else                    gtk_style_context_remove_class(sc, "on");
}

/* Keeps the mini player inside the visible part of the screen. */
static void mini_clamp(void) {
    if (!ui.mini_win || ui.mini_clamping || !gtk_widget_get_visible(ui.mini_win)) return;

    gint x, y, w, h;
    gtk_window_get_position(GTK_WINDOW(ui.mini_win), &x, &y);
    gtk_window_get_size(GTK_WINDOW(ui.mini_win), &w, &h);

    GdkDisplay *dsp = gtk_widget_get_display(ui.mini_win);
    GdkMonitor *mon = gdk_display_get_monitor_at_point(dsp, x + w / 2, y + h / 2);
    if (!mon) return;
    GdkRectangle wa;
    gdk_monitor_get_workarea(mon, &wa);

    int nx = x, ny = y;
    if (nx + w > wa.x + wa.width)  nx = wa.x + wa.width - w;
    if (ny + h > wa.y + wa.height) ny = wa.y + wa.height - h;
    if (nx < wa.x) nx = wa.x;
    if (ny < wa.y) ny = wa.y;

    if (nx != x || ny != y) {
        ui.mini_clamping = 1;
        gtk_window_move(GTK_WINDOW(ui.mini_win), nx, ny);
        ui.mini_clamping = 0;
    }
}

static gboolean mini_configure(GtkWidget *w, GdkEvent *ev, gpointer unused) {
    mini_clamp();
    return FALSE;
}

/* drag the little window by any empty part of it */
static gboolean mini_press(GtkWidget *w, GdkEventButton *ev, gpointer unused) {
    if (ev->button == 1) {
        gtk_window_begin_move_drag(GTK_WINDOW(ui.mini_win), 1,
                                   (gint)ev->x_root, (gint)ev->y_root, ev->time);
        return TRUE;
    }
    return FALSE;
}

/* the same actions as the main player's controls */
static void mini_prev(GtkButton *b, gpointer u) { skip_song(-1); }
static void mini_next(GtkButton *b, gpointer u) { skip_song(1); }
static void mini_toggle(GtkButton *b, gpointer u) { toggle_play(); }

static void mini_close(void);
static void mini_close_clicked(GtkButton *b, gpointer u) { mini_close(); }

static GtkWidget *mini_button(const char *label, GCallback cb) {
    GtkWidget *b = gtk_button_new_with_label(label);
    gtk_widget_set_can_focus(b, FALSE);
    gtk_style_context_add_class(gtk_widget_get_style_context(b), "mini-btn");
    g_signal_connect(b, "clicked", cb, NULL);
    return b;
}

/* ---- round, turning album picture ----
 * The picture is clipped to a circle (the 50% border-radius of a square) and turned about its centre while a song
 * really plays. The turn follows the frame clock, so it is even (no jitter), and stops by itself - keeping its angle -
 * when playback pauses or stops, or when nothing is loaded; it carries on from that angle when playback resumes. */
/* One full turn takes  MINI_SPIN_SECONDS = (60 * 34.5) / songBPM  seconds (clockwise). The tempo of the song is looked
 * up once per song (player_track_bpm, in a thread) and kept for the session. While it is not known - or the song has
 * none - 120 BPM is used. The BPM is limited to 30..300 so a wrong value can neither freeze nor blur the picture. */
#define MINI_SPIN_K       (60.0 * 34.5)
#define MINI_BPM_DEFAULT  120.0

static double mini_spin_seconds(void) {
    double bpm = ui.mini_bpm > 0 ? ui.mini_bpm : MINI_BPM_DEFAULT;
    if (bpm < 30.0) bpm = 30.0;
    if (bpm > 300.0) bpm = 300.0;
    return MINI_SPIN_K / bpm;
}

static GHashTable *bpm_known;                          /* song uri -> tempo (0 = the song has none), main thread only */

typedef struct { char uri[96]; char name[160]; double bpm; long status; gint64 t0; } BpmJob;

static gboolean bpm_done(gpointer data) {
    BpmJob *j = data;
    long ms = (long)((g_get_monotonic_time() - j->t0) / 1000);
    if (!bpm_known) bpm_known = g_hash_table_new_full(g_str_hash, g_str_equal, g_free, g_free);
    if (j->status == 200) {
        double *v = g_new(double, 1);
        *v = j->bpm;
        g_hash_table_replace(bpm_known, g_strdup(j->uri), v);
        activity_log(ACT_SUCCESS, "SONG_BPM", ms, NULL, "Song: %s | %.1f BPM | one turn = %.1f s", j->name, j->bpm,
                     MINI_SPIN_K / (j->bpm < 30 ? 30 : j->bpm > 300 ? 300 : j->bpm));
    } else if (j->status == 404) {                     /* nobody knows its tempo: do not ask again this session */
        double *v = g_new0(double, 1);
        g_hash_table_replace(bpm_known, g_strdup(j->uri), v);
        activity_log(ACT_WARNING, "SONG_BPM", ms, "No tempo is known for this song", "Song: %s | using %.0f BPM",
                     j->name, MINI_BPM_DEFAULT);
    } else {                                           /* network trouble: not remembered, asked again for the next song */
        activity_log(ACT_WARNING, "SONG_BPM", ms, "Could not reach the tempo service", "Song: %s | using %.0f BPM (HTTP %ld)",
                     j->name, MINI_BPM_DEFAULT, j->status);
    }
    if (strcmp(j->uri, ui.mini_bpm_uri) == 0)          /* still the playing song */
        ui.mini_bpm = j->status == 200 ? j->bpm : 0;
    g_free(j);
    return G_SOURCE_REMOVE;
}

static gpointer bpm_thread(gpointer data) {
    BpmJob *j = data;
    j->status = player_track_bpm(j->uri, &j->bpm);
    g_idle_add(bpm_done, j);
    return NULL;
}

/* Makes ui.mini_bpm the tempo of the playing song: from memory at once, else asks once in the background. */
static void mini_bpm_sync(void) {
    if (ui.mini_state == 0) return;                    /* only needed while the mini player is shown */
    if (!ui.np_uri[0]) { ui.mini_bpm = 0; ui.mini_bpm_uri[0] = '\0'; return; }
    if (strcmp(ui.mini_bpm_uri, ui.np_uri) == 0) return;          /* already known / being asked */
    snprintf(ui.mini_bpm_uri, sizeof ui.mini_bpm_uri, "%s", ui.np_uri);
    ui.mini_bpm = 0;
    const double *known = bpm_known ? g_hash_table_lookup(bpm_known, ui.np_uri) : NULL;
    if (known) { ui.mini_bpm = *known; return; }
    BpmJob *j = g_new0(BpmJob, 1);
    snprintf(j->uri, sizeof j->uri, "%s", ui.np_uri);
    copy_text(j->name, sizeof j->name, ui.np_name);
    j->t0 = g_get_monotonic_time();
    GThread *t = g_thread_new("bpm", bpm_thread, j);
    g_thread_unref(t);
}

static void mini_set_art(GdkPixbuf *pb) {
    cairo_surface_t *sf = gdk_cairo_surface_create_from_pixbuf(pb, 1, NULL);
    if (!sf || cairo_surface_status(sf) != CAIRO_STATUS_SUCCESS) {
        if (sf) cairo_surface_destroy(sf);
        return;
    }
    if (ui.mini_surf) cairo_surface_destroy(ui.mini_surf);
    ui.mini_surf = sf;
    if (ui.mini_img) gtk_widget_queue_draw(ui.mini_img);
}

static gboolean mini_art_draw(GtkWidget *w, cairo_t *cr, gpointer unused) {
    if (!ui.mini_surf) return FALSE;
    double aw = gtk_widget_get_allocated_width(w), ah = gtk_widget_get_allocated_height(w);
    double d = aw < ah ? aw : ah;                      /* a circle needs a square: the smaller side */
    double cx = aw / 2.0, cy = ah / 2.0;
    double sw = cairo_image_surface_get_width(ui.mini_surf), sh = cairo_image_surface_get_height(ui.mini_surf);

    cairo_arc(cr, cx, cy, d / 2.0, 0, 2 * G_PI);       /* the circle stays put ... */
    cairo_clip(cr);
    cairo_translate(cr, cx, cy);                       /* ... only the picture inside it turns */
    cairo_rotate(cr, ui.mini_angle * G_PI / 180.0);
    cairo_scale(cr, d / sw, d / sh);                   /* 72 -> 72 normally; keeps it exact if the size ever changes */
    cairo_set_source_surface(cr, ui.mini_surf, -sw / 2.0, -sh / 2.0);
    cairo_pattern_set_filter(cairo_get_source(cr), CAIRO_FILTER_BILINEAR);
    cairo_paint(cr);
    return FALSE;
}

/* ---- click on the picture = stop / start the turning (nothing is drawn or shown for it) ----
 * Independent of playback: it only switches the animation's permission; the music is not touched, and playback
 * changes (pause, next song, ...) neither set nor clear it. A press that moves is still a drag of the window
 * (the picture used to let those through), so the click is decided on release. */
static int mini_art_hit(GtkWidget *w, double x, double y) {
    double aw = gtk_widget_get_allocated_width(w), ah = gtk_widget_get_allocated_height(w);
    double r = (aw < ah ? aw : ah) / 2.0, dx = x - aw / 2.0, dy = y - ah / 2.0;
    return dx * dx + dy * dy <= r * r;
}

static gboolean mini_art_press(GtkWidget *w, GdkEventButton *ev, gpointer unused) {
    if (ev->button != 1 || ev->type != GDK_BUTTON_PRESS || !mini_art_hit(w, ev->x, ev->y)) return FALSE;
    ui.mini_art_down = 1;
    ui.mini_art_x = ev->x_root;
    ui.mini_art_y = ev->y_root;
    return TRUE;
}

static gboolean mini_art_motion(GtkWidget *w, GdkEventMotion *ev, gpointer unused) {
    if (!ui.mini_art_down) return FALSE;
    double dx = ev->x_root - ui.mini_art_x, dy = ev->y_root - ui.mini_art_y;
    if (dx * dx + dy * dy < 25.0) return TRUE;         /* still a click (under 5 px) */
    ui.mini_art_down = 0;                              /* it is a drag: move the window as before */
    gtk_window_begin_move_drag(GTK_WINDOW(ui.mini_win), 1, (gint)ev->x_root, (gint)ev->y_root, ev->time);
    return TRUE;
}

static gboolean mini_art_release(GtkWidget *w, GdkEventButton *ev, gpointer unused) {
    if (ev->button != 1 || !ui.mini_art_down) return FALSE;
    ui.mini_art_down = 0;
    ui.mini_spin_off = !ui.mini_spin_off;
    mini_spin_sync();                                  /* stops at once, keeping the angle / carries on from it */
    return TRUE;
}

/* Playing: turn at the song's tempo. Paused / stopped by a click: keep turning forward, slowing down smoothly (a
 * critically damped glide, starting at the speed it had) until the picture is back in its default upright position,
 * then stop and remove the tick, so nothing wakes up while it is still. */
static gboolean mini_spin_tick(GtkWidget *w, GdkFrameClock *fc, gpointer unused) {
    gint64 t = gdk_frame_clock_get_frame_time(fc);
    double dt = ui.mini_tick_last ? (double)(t - ui.mini_tick_last) / 1e6 : 0;
    ui.mini_tick_last = t;
    if (dt > 1.0) dt = 1.0;
    if (dt < 0) dt = 0;

    if (!ui.mini_home) {
        ui.mini_vel = 360.0 / mini_spin_seconds();
        if (dt > 0) ui.mini_angle = fmod(ui.mini_angle + ui.mini_vel * dt, 360.0);
    } else {
        if (dt > 0.05) dt = 0.05;
        double target = 360.0, omega = 2.0 / 0.28, x = omega * dt;
        double decay = 1.0 / (1.0 + x + 0.48 * x * x + 0.235 * x * x * x);
        double change = ui.mini_angle - target;                  /* negative: still has to turn forward */
        double tmp = (ui.mini_vel + omega * change) * dt;
        ui.mini_vel = (ui.mini_vel - omega * tmp) * decay;
        ui.mini_angle = target + (change + tmp) * decay;
        if (ui.mini_angle > target) { ui.mini_angle = target; ui.mini_vel = 0; }   /* never past the start */
        if (target - ui.mini_angle < 0.15 && ui.mini_vel < 2.0) {
            ui.mini_angle = 0;
            ui.mini_vel = 0;
            ui.mini_home = 0;
            ui.mini_tick = 0;
            ui.mini_tick_last = 0;
            gtk_widget_queue_draw(w);
            return G_SOURCE_REMOVE;
        }
        if (ui.mini_angle >= 360.0) ui.mini_angle -= 360.0;
    }
    gtk_widget_queue_draw(w);
    return G_SOURCE_CONTINUE;
}

static void mini_spin_sync(void) {
    if (!ui.mini_img) return;
    int shown = ui.mini_state != 0 && ui.np_uri[0];
    int want = shown && ui.playing && !ui.mini_spin_off;
    if (want) ui.mini_home = 0;
    else if (shown && ui.mini_angle > 0.5 && ui.mini_angle < 359.5) ui.mini_home = 1;   /* paused: glide back upright */
    else { ui.mini_home = 0; ui.mini_angle = 0; ui.mini_vel = 0; }                    /* already (almost) upright */
    int run = want || ui.mini_home;
    if (run && !ui.mini_tick) {
        ui.mini_tick_last = 0;                         /* the first step only records the time: smooth restart */
        ui.mini_tick = gtk_widget_add_tick_callback(ui.mini_img, mini_spin_tick, NULL, NULL);
    } else if (!run && ui.mini_tick) {
        gtk_widget_remove_tick_callback(ui.mini_img, ui.mini_tick);
        ui.mini_tick = 0;
        ui.mini_tick_last = 0;
        if (!shown) { ui.mini_angle = 0; ui.mini_vel = 0; gtk_widget_queue_draw(ui.mini_img); }   /* hidden: upright */
    }
}

static void mini_build(void) {
    ui.mini_win = gtk_window_new(GTK_WINDOW_TOPLEVEL);
    gtk_window_set_decorated(GTK_WINDOW(ui.mini_win), FALSE);
    gtk_window_set_resizable(GTK_WINDOW(ui.mini_win), FALSE);
    gtk_window_set_keep_above(GTK_WINDOW(ui.mini_win), TRUE);
    gtk_window_set_skip_taskbar_hint(GTK_WINDOW(ui.mini_win), TRUE);
    gtk_window_set_accept_focus(GTK_WINDOW(ui.mini_win), FALSE);   /* keys stay with the main window */
    gtk_style_context_add_class(gtk_widget_get_style_context(ui.mini_win), "mini-window");

    GdkScreen *scr = gtk_widget_get_screen(ui.mini_win);           /* see-through corners and shadow */
    GdkVisual *vis = gdk_screen_get_rgba_visual(scr);
    if (vis && gdk_screen_is_composited(scr)) gtk_widget_set_visual(ui.mini_win, vis);
    gtk_widget_set_app_paintable(ui.mini_win, TRUE);

    GtkWidget *ev = gtk_event_box_new();
    gtk_event_box_set_visible_window(GTK_EVENT_BOX(ev), FALSE);
    g_signal_connect(ev, "button-press-event", G_CALLBACK(mini_press), NULL);
    gtk_container_add(GTK_CONTAINER(ui.mini_win), ev);

    GtkWidget *card = gtk_box_new(GTK_ORIENTATION_HORIZONTAL, 12);
    gtk_style_context_add_class(gtk_widget_get_style_context(card), "mini-card");
    gtk_widget_set_margin_start(card, 16);  gtk_widget_set_margin_end(card, 16);
    gtk_widget_set_margin_top(card, 14);    gtk_widget_set_margin_bottom(card, 18);
    gtk_container_add(GTK_CONTAINER(ev), card);

    ui.mini_img = gtk_drawing_area_new();                    /* round picture; turns while a song plays */
    gtk_widget_set_size_request(ui.mini_img, 72, 72);
    gtk_widget_set_valign(ui.mini_img, GTK_ALIGN_CENTER);
    gtk_widget_set_halign(ui.mini_img, GTK_ALIGN_CENTER);    /* never stretched: always a true circle */
    g_signal_connect(ui.mini_img, "draw", G_CALLBACK(mini_art_draw), NULL);
    gtk_widget_add_events(ui.mini_img, GDK_BUTTON_PRESS_MASK | GDK_BUTTON_RELEASE_MASK | GDK_BUTTON1_MOTION_MASK);
    g_signal_connect(ui.mini_img, "button-press-event", G_CALLBACK(mini_art_press), NULL);
    g_signal_connect(ui.mini_img, "motion-notify-event", G_CALLBACK(mini_art_motion), NULL);
    g_signal_connect(ui.mini_img, "button-release-event", G_CALLBACK(mini_art_release), NULL);
    gtk_box_pack_start(GTK_BOX(card), ui.mini_img, FALSE, FALSE, 0);

    GtkWidget *col = gtk_box_new(GTK_ORIENTATION_VERTICAL, 4);
    gtk_widget_set_size_request(col, 210, -1);
    gtk_box_pack_start(GTK_BOX(card), col, TRUE, TRUE, 0);

    ui.mini_title  = make_label("", 0);
    ui.mini_artist = make_label("", 1);
    gtk_box_pack_start(GTK_BOX(col), ui.mini_title, FALSE, FALSE, 0);
    gtk_box_pack_start(GTK_BOX(col), ui.mini_artist, FALSE, FALSE, 0);

    GtkWidget *row = gtk_box_new(GTK_ORIENTATION_HORIZONTAL, 6);
    gtk_widget_set_margin_top(row, 4);
    gtk_box_pack_start(GTK_BOX(col), row, FALSE, FALSE, 0);
    gtk_box_pack_start(GTK_BOX(row), mini_button("Prev", G_CALLBACK(mini_prev)), FALSE, FALSE, 0);
    ui.mini_play = mini_button("Play", G_CALLBACK(mini_toggle));
    gtk_box_pack_start(GTK_BOX(row), ui.mini_play, FALSE, FALSE, 0);
    gtk_box_pack_start(GTK_BOX(row), mini_button("Next", G_CALLBACK(mini_next)), FALSE, FALSE, 0);
    GtkWidget *x = mini_button("\xE2\x88\x92", G_CALLBACK(mini_close_clicked));   /* minus sign */
    gtk_box_pack_end(GTK_BOX(row), x, FALSE, FALSE, 0);

    g_signal_connect(ui.mini_win, "configure-event", G_CALLBACK(mini_configure), NULL);
    gtk_widget_show_all(ev);
}

static void mini_refresh(void) {
    if (!ui.mini_win) return;

    if (ui.np_uri[0]) {
        char *m = g_markup_printf_escaped("<span weight=\"bold\">%s</span>", ui.np_name);
        label_markup_once(ui.mini_title, m);
        g_free(m);
        label_text_once(ui.mini_artist, ui.np_artist_s);
    } else {
        label_markup_once(ui.mini_title, "<span weight=\"bold\">Nothing playing</span>");
        label_text_once(ui.mini_artist, "");
    }
    const char *pl = ui.playing ? "Pause" : "Play";
    if (strcmp(gtk_button_get_label(GTK_BUTTON(ui.mini_play)), pl) != 0)
        gtk_button_set_label(GTK_BUTTON(ui.mini_play), pl);

    GdkPixbuf *pb = art_lookup(ui.np_img_url);
    if (pb) {
        if (strcmp(ui.mini_img_set, ui.np_img_url) != 0) {
            GdkPixbuf *sc = gdk_pixbuf_scale_simple(pb, 72, 72, GDK_INTERP_BILINEAR);
            if (sc) {
                mini_set_art(sc);
                g_object_unref(sc);
                snprintf(ui.mini_img_set, sizeof ui.mini_img_set, "%s", ui.np_img_url);
            }
        }
    } else if (ui.mini_img_set[0] || !ui.mini_surf) {
        GdkPixbuf *ph = placeholder_pixbuf();          /* no stale picture of the last song */
        if (ph) mini_set_art(ph);
        ui.mini_img_set[0] = '\0';
    }
    mini_bpm_sync();
    mini_spin_sync();
}

static void mini_update(void) {
    if (ui.mini_state != 0) mini_refresh();            /* nothing to refresh while it is closed */
}

static void mini_open(void) {
    if (ui.mini_state == 1) return;                    /* already open: never a second one */
    activity_log(ACT_SUCCESS, "OPEN_PANEL", -1, NULL, "Window: Mini player");

    if (!ui.mini_win) mini_build();
    mini_refresh();

    if (ui.mini_state == 0) {                          /* start in the lower right corner */
        gtk_widget_set_opacity(ui.mini_win, 0.0);
        gtk_widget_show(ui.mini_win);

        GdkDisplay *dsp = gtk_widget_get_display(ui.win);
        GdkMonitor *mon = gdk_display_get_monitor_at_window(dsp, gtk_widget_get_window(ui.win));
        GtkRequisition nat;
        gtk_widget_get_preferred_size(ui.mini_win, NULL, &nat);
        if (mon) {
            GdkRectangle wa;
            gdk_monitor_get_workarea(mon, &wa);
            gtk_window_move(GTK_WINDOW(ui.mini_win),
                            wa.x + wa.width - nat.width - 24, wa.y + wa.height - nat.height - 24);
        }
    }
    ui.mini_state = 1;
    poll_resched();                                    /* the mini player shows the song: keep the normal rate */
    mini_bpm_sync();                                   /* tempo of the song that is playing right now */
    mini_spin_sync();                                  /* already playing: start turning as it appears */
    mini_set_buttons();
    if (!mini_fade_id) mini_fade_id = g_timeout_add(16, mini_fade_cb, NULL);
}

static void mini_close(void) {
    if (ui.mini_state != 1) return;                    /* not open, or already closing */
    activity_log(ACT_SUCCESS, "CLOSE_PANEL", -1, NULL, "Window: Mini player");
    ui.mini_state = 2;
    mini_set_buttons();
    if (!mini_fade_id) mini_fade_id = g_timeout_add(16, mini_fade_cb, NULL);
}

static void on_mini_plus(GtkButton *b, gpointer unused)  { mini_open(); }
static void on_mini_minus(GtkButton *b, gpointer unused) { mini_close(); }

static void on_queue_btn(GtkButton *b, gpointer unused) {
    if (ui.logged_in) toggle_queue_view();
}

static void on_dev_btn(GtkButton *b, gpointer unused) {
    play_on_selected_device();
}

/* Q: adds the song in the middle of the carousel to the end of your queue. */
static gboolean queue_reload_cb(gpointer unused) {
    if (ui.view_queue) {
        GThread *t = g_thread_new("queue", queue_thread, NULL);
        g_thread_unref(t);
    }
    return G_SOURCE_REMOVE;
}

static gboolean toast_hide_cb(gpointer unused) {
    ui.toast_id = 0;
    if (ui.toast) gtk_widget_hide(ui.toast);
    return G_SOURCE_REMOVE;
}

/* A message that pops up over the window for 2.5 s. */
static void show_toast(const char *msg) {
    if (!ui.toast) return;
    gtk_label_set_text(GTK_LABEL(ui.toast), msg);
    gtk_widget_show(ui.toast);
    if (ui.toast_id) g_source_remove(ui.toast_id);
    ui.toast_id = g_timeout_add(2500, toast_hide_cb, NULL);
}

static void queue_uri(const char *uri, const char *name) {
    if (!ui.logged_in || !uri || !*uri) return;

    {   /* the request path must fit its buffer (a cut address would add a different song or nothing) */
        size_t colons = 0;
        for (const char *p = uri; *p; p++) if (*p == ':') colons++;
        if (strlen(uri) + 2 * colons + sizeof "/queue?uri=" > sizeof ((Job *)0)->path) {
            show_toast("This song cannot be added to the queue");
            activity_log(ACT_FAILED, "QUEUE_ADD", -1, "Song address is too long for a queue request", "%s", name);
            return;
        }
    }

    if (qadded_find(uri) >= 0) {              /* already waiting in the queue: do not add it again */
        char tm[300];
        snprintf(tm, sizeof tm, "Already in your queue:  %s", name);
        show_toast(tm);
        activity_log(ACT_CANCELLED, "QUEUE_ADD", -1, "Song is already in the queue", "%s", name);
        return;
    }
    qadded_add(uri);

    char enc[160];
    size_t k = 0;
    for (const char *p = uri; *p && k + 4 < sizeof enc; p++) {
        if (*p == ':') { memcpy(enc + k, "%3A", 3); k += 3; }
        else           enc[k++] = *p;
    }
    enc[k] = '\0';

    Job *j = g_new0(Job, 1);                 /* only adds: the playing song is not touched */
    snprintf(j->method, sizeof j->method, "POST");
    int pn = snprintf(j->path, sizeof j->path, "/queue?uri=%s", enc);   /* length was checked above; the result is checked again */
    if (pn < 0 || (size_t)pn >= sizeof j->path) {
        g_free(j);
        show_toast("This song cannot be added to the queue");
        return;
    }
    snprintf(j->okmsg, sizeof j->okmsg, "Added to queue: %s", name);
    j->flash = 1;
    start_job(j);

    char tm[300];
    snprintf(tm, sizeof tm, "+  Added to queue:  %s", name);
    show_toast(tm);                          /* seen at once, not after Spotify answers */

    g_atomic_int_set(&poll_reset, 1);        /* refresh the carousel's queue */
    if (ui.view_queue) g_timeout_add(1200, queue_reload_cb, NULL);   /* keep an open queue list current */
}

/* Q: adds the highlighted song (song list open with T) or, otherwise, the
 * song in the middle of the carousel. It never starts playing it. */
static void queue_key(void) {
    if (!ui.logged_in) return;

    if (ui.view_tracks && !ui.view_queue && !ui.view_dev) {
        GtkTreeModel *m;
        GtkTreeIter it;
        if (gtk_tree_selection_get_selected(
                gtk_tree_view_get_selection(GTK_TREE_VIEW(ui.tree)), &m, &it)) {
            gchar *label = NULL, *uri = NULL;
            gtk_tree_model_get(m, &it, 0, &label, 1, &uri, -1);
            if (uri && *uri) queue_uri(uri, label ? label : "song");
            g_free(label);
            g_free(uri);
            return;
        }
    }

    if (cn <= 0) return;
    int mid = (int)floor(car_cx + 0.5);
    if (mid < 0) mid = 0;
    if (mid > cn - 1) mid = cn - 1;
    queue_uri(citems[mid].uri, citems[mid].name);
}

/* D: move the music to the Spotify app on this PC. */
static void play_here(void) {
    if (!ui.logged_in) return;

    Job *j = g_new0(Job, 1);
    j->here = 1;
    snprintf(j->okmsg, sizeof j->okmsg, "Playing on this PC");
    start_job(j);
}

static gboolean on_key(GtkWidget *w, GdkEventKey *ev, gpointer unused) {
    /* never steal keys while typing in a text box */
    GtkWidget *f = gtk_window_get_focus(GTK_WINDOW(w));
    if (f && (GTK_IS_EDITABLE(f) || GTK_IS_TEXT_VIEW(f))) return FALSE;
    if (ev->state & GDK_MOD1_MASK) return FALSE;      /* Alt+key belongs to the window system / menus */

    switch (ev->keyval) {
    case GDK_KEY_Escape:
        g_atomic_int_set(&app_closing, 1);       /* waiting results must not run once the loop ends */
        gtk_main_quit();
        return TRUE;

    case GDK_KEY_q:
    case GDK_KEY_Q:
        if (ev->state & (GDK_CONTROL_MASK | GDK_MOD1_MASK)) return FALSE;   /* leave Ctrl/Alt+Q alone */
        queue_key();
        return TRUE;

    case GDK_KEY_d:
    case GDK_KEY_D:
        play_here();
        return TRUE;

    case GDK_KEY_space:
        toggle_play();
        return TRUE;

    case GDK_KEY_Right:
        skip_song(1);
        return TRUE;

    case GDK_KEY_Left:
        skip_song(-1);
        return TRUE;

    case GDK_KEY_Up:
        move_selection(-1);
        return TRUE;

    case GDK_KEY_Down:
        move_selection(+1);
        return TRUE;

    case GDK_KEY_Return:
    case GDK_KEY_KP_Enter:
        activate_selected();
        return TRUE;

    case GDK_KEY_a:
    case GDK_KEY_A:
        toggle_queue_view();
        return TRUE;

    case GDK_KEY_v:
    case GDK_KEY_V:
        if (ui.view_dev) close_devices_view();
        else             open_devices_view();
        return TRUE;

    case GDK_KEY_plus:
    case GDK_KEY_equal:
    case GDK_KEY_KP_Add:
        mini_open();
        return TRUE;

    case GDK_KEY_minus:
    case GDK_KEY_KP_Subtract:
        mini_close();
        return TRUE;

    case GDK_KEY_bracketright:
        change_volume(5);
        return TRUE;

    case GDK_KEY_bracketleft:
        change_volume(-5);
        return TRUE;

    case GDK_KEY_6:
        open_queue_view();
        return TRUE;

    case GDK_KEY_7:
        close_queue_view();
        return TRUE;

    case GDK_KEY_s:
    case GDK_KEY_S:
        toggle_shuffle();
        return TRUE;

    case GDK_KEY_r:
    case GDK_KEY_R:
        toggle_repeat();
        return TRUE;

    case GDK_KEY_h:
    case GDK_KEY_H:                          /* show / hide the shortcut help (hidden in small windows) */
        ui.hint_force = !ui.hint_force;
        activity_log(ACT_SUCCESS, ui.hint_force ? "OPEN_PANEL" : "CLOSE_PANEL", -1, NULL, "Panel: Shortcut help");
        update_hint_visibility();
        return TRUE;

    case GDK_KEY_t:
    case GDK_KEY_T:
        toggle_tracks_view();
        return TRUE;

    case GDK_KEY_slash:                      /* search the songs on screen */
        search_open();
        return TRUE;

    case GDK_KEY_f:
    case GDK_KEY_F:
        if (!(ev->state & GDK_CONTROL_MASK)) break;
        search_open();
        return TRUE;

    case GDK_KEY_p:
    case GDK_KEY_P: {                        /* swap between the two playlists under the pictures */
        static guint32 last_p;
        if (ev->state & (GDK_CONTROL_MASK | GDK_MOD1_MASK)) return FALSE;
        if (ev->time - last_p < 150) return TRUE;           /* key auto-repeat / bounce: one swap only */
        last_p = ev->time;
        strip_swap();
        return TRUE;
    }

    case GDK_KEY_F5:
        activity_log(ACT_PENDING, "REFRESH_PLAYLISTS", -1, NULL, "F5: playlists and loaded songs are read again");
        plcache_clear();                     /* reload really reloads: songs too, not only the names */
        if (!ui.view_tracks) {
            ui.tracks_pl[0] = '\0';
            ui.preload_ctx[0] = '\0';        /* the playing playlist's songs are read again */
        }
        load_playlists();
        return TRUE;
    }
    return FALSE;
}

static void on_row_activated(GtkTreeView *tv, GtkTreePath *path,
                             GtkTreeViewColumn *col, gpointer unused) {
    activate_selected();
}

/* ---------- seek bar ---------- */

static gboolean on_scale_press(GtkWidget *w, GdkEventButton *ev, gpointer unused) {
    if (ui.logged_in && ui.dur_ms > 0) ui.seeking = 1;
    return FALSE;
}

/* While dragging, show the time under the handle. */
static void on_scale_changed(GtkRange *range, gpointer unused) {
    if (!ui.seeking || ui.dur_ms <= 0) return;

    long p = (long)(gtk_range_get_value(range) / 1000.0 * (double)ui.dur_ms) / 1000;
    long d = ui.dur_ms / 1000;
    char buf[64];
    snprintf(buf, sizeof buf, "%ld:%02ld / %ld:%02ld", p / 60, p % 60, d / 60, d % 60);
    gtk_label_set_text(GTK_LABEL(ui.time), buf);
}

static gboolean on_scale_release(GtkWidget *w, GdkEventButton *ev, gpointer unused) {
    if (!ui.seeking) return FALSE;
    ui.seeking = 0;

    long pos = (long)(gtk_range_get_value(GTK_RANGE(w)) / 1000.0 * (double)ui.dur_ms);
    ui.prog_ms = pos;
    ui.seek_until = g_get_monotonic_time() + 2 * G_USEC_PER_SEC;
    update_time();

    char path[64];
    snprintf(path, sizeof path, "/seek?position_ms=%ld", pos);
    send_cmd("PUT", path, "Jumped to new position");
    return FALSE;
}

/* ---------- window ---------- */

static GtkWidget *make_label(const char *text, int dim) {
    GtkWidget *l = gtk_label_new(text);
    gtk_label_set_xalign(GTK_LABEL(l), 0.0f);
    gtk_label_set_ellipsize(GTK_LABEL(l), PANGO_ELLIPSIZE_END);
    if (dim)
        gtk_style_context_add_class(gtk_widget_get_style_context(l), "dim");
    return l;
}

/* Clicking a picture plays that song (scrolling never does). */
static void car_play(int i) {
    if (!ui.logged_in || i < 0 || i >= cn) return;
    const CItem *c = &citems[i];

    car_select(i);

    if (ui.current_uri[0] && strcmp(c->uri, ui.current_uri) == 0) {
        toggle_play();                      /* the song that is already playing */
        return;
    }

    Job *j = g_new0(Job, 1);
    snprintf(j->uri, sizeof j->uri, "%s", c->uri);
    { char nm[160]; copy_text(nm, sizeof nm, c->name); snprintf(j->okmsg, sizeof j->okmsg, "Playing: %s", nm); }
    if (car_mini) {                         /* this song and the ones after it, so the music keeps going */
        int n = 0;
        for (int k = i; k < cn && n < 25; k++)
            snprintf(j->uris[n++], sizeof j->uris[0], "%s", citems[k].uri);
        j->multi = n;
    } else if (ui.tracks_pl[0]) {           /* inside its playlist */
        j->track = 1;
        snprintf(j->id, sizeof j->id, "%s", ui.tracks_pl);
    } else {
        j->single = 1;
    }
    select_song(j, c->uri, c->name, c->artist, c->big[0] ? c->big : c->img);
}

#ifdef _WIN32
/* Num Lock anywhere: window up -> minimize, otherwise bring it to the front. */
static gboolean show_window_cb(gpointer unused) {
    if (!ui.win) return G_SOURCE_REMOVE;
    if (gtk_window_is_active(GTK_WINDOW(ui.win))) {   /* already up: bring it down */
        activity_log(ACT_SUCCESS, "NUMLOCK_WINDOW", -1, NULL, "Window minimized");
        gtk_window_iconify(GTK_WINDOW(ui.win));
        return G_SOURCE_REMOVE;
    }

    gtk_window_deiconify(GTK_WINDOW(ui.win));
    gtk_window_present(GTK_WINDOW(ui.win));
    activity_log(ACT_SUCCESS, "NUMLOCK_WINDOW", -1, NULL, "Window brought forward");

    HWND h = (HWND)gdk_win32_window_get_handle(gtk_widget_get_window(ui.win));
    if (h) {
        if (IsIconic(h)) ShowWindow(h, SW_RESTORE);
        SetWindowPos(h, HWND_TOPMOST, 0, 0, 0, 0, SWP_NOMOVE | SWP_NOSIZE);
        SetWindowPos(h, HWND_NOTOPMOST, 0, 0, 0, 0, SWP_NOMOVE | SWP_NOSIZE);
        SetForegroundWindow(h);
    }
    center_cards_on_current(1);            /* playing song in the middle */
    return G_SOURCE_REMOVE;
}

static LRESULT CALLBACK numlock_hook(int code, WPARAM wp, LPARAM lp) {
    if (code == HC_ACTION && wp == WM_KEYDOWN) {
        const KBDLLHOOKSTRUCT *k = (const KBDLLHOOKSTRUCT *)lp;
        if (k->vkCode == VK_NUMLOCK && !(k->flags & LLKHF_INJECTED))
            g_idle_add(show_window_cb, NULL);
    }
    return CallNextHookEx(NULL, code, wp, lp);   /* the key still works normally */
}

static DWORD WINAPI hook_thread(LPVOID unused) {
    SetWindowsHookExA(WH_KEYBOARD_LL, numlock_hook, GetModuleHandleA(NULL), 0);

    MSG m;                                  /* a hook needs a message loop */
    while (GetMessage(&m, NULL, 0, 0) > 0) {
        TranslateMessage(&m);
        DispatchMessage(&m);
    }
    return 0;
}
#endif

static void apply_css(void) {
    static const char *css_text =
        "window { background-color: #121212; }"
        "label { color: #ffffff; text-shadow: 0 1px 3px rgba(0,0,0,0.55); }"
        ".dim { color: #b3b3b3; }"
        ".toast { background: #1db954; color: #000; font-weight: bold; padding: 8px 18px; border-radius: 18px; }"
        ".dimmer { color: #727272; }"
        ".plswitch button { padding: 3px 12px; min-height: 18px; border-radius: 16px; opacity: 0.75;"
        "  transition: background-color 180ms ease, color 180ms ease, opacity 180ms ease, box-shadow 180ms ease; }"
        ".plswitch button:hover { background-color: #3a3a3a; opacity: 1; }"
        ".plswitch button.pl-active { background-color: #1db954; color: #000000; opacity: 1;"
        "  box-shadow: 0 0 0 2px rgba(29,185,84,0.35); }"
        ".plswitch button.pl-active:hover { background-color: #1ed760; }"
        ".plswitch button.pl-loading { opacity: 0.5; }"
        ".pl-now { color: #1db954; font-weight: bold; }"
        ".pl-active .pl-now { color: #000000; }"
        "eventbox { background-color: #121212; }"
        "iconview { background-color: #181818; }"
        "iconview.cell:selected { background-color: #1db954; }"
        "treeview.view { background-color: rgba(18,18,18,0.55); color: #ffffff; font-size: 14px; }"
        "treeview.view:hover { background-color: rgba(255,255,255,0.08); }"
        "treeview.view:selected { background-color: #1db954; color: #000000; }"
        "scrolledwindow, scrolledwindow viewport { background-color: transparent; }"
        "button { background-image: none; background-color: #282828; color: #ffffff;"
        "  border: none; border-radius: 18px; padding: 8px 18px; min-height: 20px;"
        "  box-shadow: none; text-shadow: none;"
        "  transition: background-color 150ms ease, color 150ms ease; }"
        "button label { color: inherit; text-shadow: none; }"
        "window.mini-window { background-color: transparent; }"
        ".mini-card { background-color: rgba(22,22,22,0.92); border-radius: 18px; padding: 12px;"
        "  border: 1px solid rgba(255,255,255,0.07); box-shadow: 0 8px 22px rgba(0,0,0,0.55); }"
        "button.mini-btn { padding: 4px 12px; min-height: 0; font-size: 12px; border-radius: 14px; }"
        "button.round { padding: 2px 0; min-width: 36px; min-height: 0; font-size: 16px;"
        "  font-weight: bold; border-radius: 18px; }"
        "button.small { padding: 2px 14px; min-height: 0; font-size: 12px; }"
        "window.compact button { padding: 5px 12px; min-height: 0; }"
        "button:hover { background-color: #3a3a3a; }"
        "button:active { background-color: #1db954; color: #000000; }"
        "button.on { background-color: #1db954; color: #000000; }"
        "button.on:hover { background-color: #1ed760; }"
        "button.on label { color: #000000; }"
        "scrolledwindow { border-radius: 8px; }"
        "label.ok { color: #1db954; transition: color 300ms ease; }"
        ".np-card { background-color: #1f1f1f; border-left: 3px solid #1db954;"
        "  border-radius: 8px; padding: 10px 12px; }"
        "label.np-status { color: #1db954; font-size: 12px; }"
        "treeview.view { padding: 2px 4px; }"
        "scrollbar { background-color: transparent; border: none; }"
        "scrollbar slider { background-color: #535353; border-radius: 6px; min-width: 8px;"
        "  transition: background-color 150ms ease; }"
        "scrollbar slider:hover { background-color: #7a7a7a; }"
        "scale trough { min-height: 6px; background-color: #404040; border: none; }"
        "scale highlight { background-color: #1db954; border: none; }"
        "scale slider { background-color: #ffffff; background-image: none; border: none; }";

    GtkCssProvider *css = gtk_css_provider_new();
    gtk_css_provider_load_from_data(css, css_text, -1, NULL);
    gtk_style_context_add_provider_for_screen(
        gdk_screen_get_default(), GTK_STYLE_PROVIDER(css),
        GTK_STYLE_PROVIDER_PRIORITY_APPLICATION);
    g_object_unref(css);
}
int ui_run(void) {
    activity_init();
    activity_log(ACT_SUCCESS, "APP_START", -1, NULL, "Spotify Controller | build %s %s", __DATE__, __TIME__);
    gtk_init(NULL, NULL);

    ui.volume = -1;
    thumbs  = lru_new("Thumbnail cache", THUMB_BUDGET, THUMB_ENTRIES, cover_free);
    bigs    = lru_new("Big-cover cache", BIG_BUDGET, BIG_ENTRIES, cover_free);
    plcache = lru_new("Playlist cache", PL_BUDGET, PL_ENTRIES, plcache_free);
    lru_set_pin(plcache, plcache_pin, NULL);
    pending = g_hash_table_new_full(g_str_hash, g_str_equal, g_free, NULL);
    failed  = g_hash_table_new_full(g_str_hash, g_str_equal, g_free, NULL);
    ui.pool = g_thread_pool_new(thumb_worker, NULL, 6, FALSE, NULL);
    g_thread_pool_set_sort_function(ui.pool, job_order, NULL);
    apply_css();

    ui.win = gtk_window_new(GTK_WINDOW_TOPLEVEL);
    gtk_window_set_title(GTK_WINDOW(ui.win), "Spotify Controller");
    gtk_window_set_default_size(GTK_WINDOW(ui.win), 620, 900);
    g_signal_connect(ui.win, "destroy", G_CALLBACK(on_win_destroy), NULL);
    g_signal_connect(ui.win, "key-press-event", G_CALLBACK(on_key), NULL);
    g_signal_connect(ui.win, "window-state-event", G_CALLBACK(on_win_state), NULL);
    g_signal_connect(ui.win, "focus-in-event", G_CALLBACK(on_focus_in), NULL);
    g_signal_connect(ui.win, "size-allocate", G_CALLBACK(on_win_size), NULL);

    GtkWidget *box = gtk_box_new(GTK_ORIENTATION_VERTICAL, 8);
    gtk_container_set_border_width(GTK_CONTAINER(box), 16);
    ui.main_box = box;
    ui.list_open = 1;
    ui.lay_wide = ui.lay_tier = -1;                         /* decided on the first resize */

    GtkWidget *top = gtk_box_new(GTK_ORIENTATION_VERTICAL, 8);   /* cover, song info, progress */
    GtkWidget *bot = gtk_box_new(GTK_ORIENTATION_VERTICAL, 8);   /* playlists, buttons, help */
    ui.pane_top = top;
    ui.pane_bot = bot;
    gtk_box_pack_start(GTK_BOX(box), top, FALSE, FALSE, 0);
    gtk_box_pack_start(GTK_BOX(box), bot, TRUE, TRUE, 0);

    GtkWidget *overlay = gtk_overlay_new();                 /* ambient background under everything */
    fx_seed(FX_NEUTRAL);
    ui.bg = gtk_drawing_area_new();
    g_signal_connect(ui.bg, "draw", G_CALLBACK(bg_draw), NULL);
    for (int i = 0; i < 3; i++)
        for (int k = 0; k < 3; k++)
            ui.bg_cur[i][k] = ui.bg_tgt[i][k] = BG_BASE;
    gtk_container_add(GTK_CONTAINER(overlay), ui.bg);
    gtk_overlay_add_overlay(GTK_OVERLAY(overlay), box);

    ui.toast = gtk_label_new("");
    gtk_style_context_add_class(gtk_widget_get_style_context(ui.toast), "toast");
    gtk_label_set_ellipsize(GTK_LABEL(ui.toast), PANGO_ELLIPSIZE_END);
    gtk_label_set_max_width_chars(GTK_LABEL(ui.toast), 60);
    gtk_widget_set_halign(ui.toast, GTK_ALIGN_CENTER);
    gtk_widget_set_valign(ui.toast, GTK_ALIGN_START);
    gtk_widget_set_margin_top(ui.toast, 14);
    gtk_widget_set_no_show_all(ui.toast, TRUE);          /* hidden until a message comes */
    gtk_overlay_add_overlay(GTK_OVERLAY(overlay), ui.toast);
    gtk_overlay_set_overlay_pass_through(GTK_OVERLAY(overlay), ui.toast, TRUE);
    gtk_container_add(GTK_CONTAINER(ui.win), overlay);

    /* one carousel: the song in the middle is the biggest */
    ui.car = gtk_drawing_area_new();
    gtk_widget_set_size_request(ui.car, -1, CAR_H);
    gtk_widget_add_events(ui.car, GDK_BUTTON_PRESS_MASK | GDK_BUTTON_RELEASE_MASK |
                                  GDK_BUTTON_MOTION_MASK | GDK_SCROLL_MASK |
                                  GDK_SMOOTH_SCROLL_MASK);
    g_signal_connect(ui.car, "draw", G_CALLBACK(car_draw), NULL);
    g_signal_connect(ui.car, "scroll-event", G_CALLBACK(car_scroll), NULL);
    g_signal_connect(ui.car, "button-press-event", G_CALLBACK(car_press), NULL);
    g_signal_connect(ui.car, "motion-notify-event", G_CALLBACK(car_motion), NULL);
    g_signal_connect(ui.car, "button-release-event", G_CALLBACK(car_release), NULL);
    g_signal_connect(ui.car, "realize", G_CALLBACK(car_realize), NULL);
    gtk_widget_set_valign(ui.car, GTK_ALIGN_CENTER);       /* centered when the list is folded */
    gtk_box_pack_start(GTK_BOX(top), ui.car, FALSE, FALSE, 0);

    pls.box = gtk_box_new(GTK_ORIENTATION_HORIZONTAL, 8);      /* the two-playlist switch */
    gtk_style_context_add_class(gtk_widget_get_style_context(pls.box), "plswitch");
    gtk_widget_set_halign(pls.box, GTK_ALIGN_CENTER);
    gtk_widget_set_no_show_all(pls.box, TRUE);                 /* shown by strip_update only */
    for (int i = 0; i < 2; i++) {
        pls.btn[i] = gtk_button_new();
        gtk_widget_set_can_focus(pls.btn[i], FALSE);           /* keys keep working as before */
        GtkWidget *row = gtk_box_new(GTK_ORIENTATION_HORIZONTAL, 6);
        pls.img[i] = gtk_image_new();
        gtk_widget_set_no_show_all(pls.img[i], TRUE);
        pls.now[i] = gtk_label_new("\xE2\x99\xAA");               /* note: this one is playing */
        gtk_style_context_add_class(gtk_widget_get_style_context(pls.now[i]), "pl-now");
        gtk_widget_set_no_show_all(pls.now[i], TRUE);
        pls.lbl[i] = gtk_label_new("");
        gtk_label_set_ellipsize(GTK_LABEL(pls.lbl[i]), PANGO_ELLIPSIZE_END);
        gtk_label_set_max_width_chars(GTK_LABEL(pls.lbl[i]), 22);
        gtk_box_pack_start(GTK_BOX(row), pls.img[i], FALSE, FALSE, 0);
        gtk_box_pack_start(GTK_BOX(row), pls.now[i], FALSE, FALSE, 0);
        gtk_box_pack_start(GTK_BOX(row), pls.lbl[i], FALSE, FALSE, 0);
        gtk_container_add(GTK_CONTAINER(pls.btn[i]), row);
        g_signal_connect(pls.btn[i], "clicked", G_CALLBACK(strip_clicked), GINT_TO_POINTER(i));
        gtk_box_pack_start(GTK_BOX(pls.box), pls.btn[i], FALSE, FALSE, 0);
        gtk_widget_show_all(pls.btn[i]);
        gtk_widget_hide(pls.img[i]);
        gtk_widget_hide(pls.now[i]);
    }
    gtk_box_pack_start(GTK_BOX(top), pls.box, FALSE, FALSE, 0);

    search_entry = gtk_search_entry_new();                     /* hidden until / or Ctrl+F */
    gtk_entry_set_placeholder_text(GTK_ENTRY(search_entry), "Search songs in this playlist   (Esc closes)");
    gtk_widget_set_no_show_all(search_entry, TRUE);
    gtk_widget_set_halign(search_entry, GTK_ALIGN_CENTER);
    gtk_widget_set_size_request(search_entry, 320, -1);
    g_signal_connect(search_entry, "search-changed", G_CALLBACK(search_changed), NULL);
    g_signal_connect(search_entry, "activate", G_CALLBACK(search_activate), NULL);
    g_signal_connect(search_entry, "stop-search", G_CALLBACK(search_stop), NULL);
    gtk_box_pack_start(GTK_BOX(top), search_entry, FALSE, FALSE, 0);

    ui.warn = make_label("", 1);                           /* only shown when pictures fail */
    gtk_label_set_ellipsize(GTK_LABEL(ui.warn), PANGO_ELLIPSIZE_NONE);
    gtk_label_set_line_wrap(GTK_LABEL(ui.warn), TRUE);
    gtk_label_set_xalign(GTK_LABEL(ui.warn), 0.5f);
    gtk_widget_set_no_show_all(ui.warn, TRUE);
    gtk_box_pack_start(GTK_BOX(top), ui.warn, FALSE, FALSE, 0);

    ui.track = make_label("", 0);
    gtk_label_set_xalign(GTK_LABEL(ui.track), 0.5f);
    gtk_label_set_markup(GTK_LABEL(ui.track),
        "<span size=\"large\" weight=\"bold\">Spotify Controller</span>");
    gtk_box_pack_start(GTK_BOX(top), ui.track, FALSE, FALSE, 0);

    ui.artist = make_label("Logging in... approve access in your browser", 1);
    gtk_label_set_xalign(GTK_LABEL(ui.artist), 0.5f);
    gtk_box_pack_start(GTK_BOX(top), ui.artist, FALSE, FALSE, 0);

    ui.bar = gtk_scale_new_with_range(GTK_ORIENTATION_HORIZONTAL, 0, 1000, 1);
    gtk_scale_set_draw_value(GTK_SCALE(ui.bar), FALSE);
    g_signal_connect(ui.bar, "button-press-event", G_CALLBACK(on_scale_press), NULL);
    g_signal_connect_after(ui.bar, "button-release-event", G_CALLBACK(on_scale_release), NULL);
    g_signal_connect(ui.bar, "value-changed", G_CALLBACK(on_scale_changed), NULL);
    gtk_box_pack_start(GTK_BOX(top), ui.bar, FALSE, FALSE, 6);

    ui.time = make_label("0:00 / 0:00", 1);
    gtk_box_pack_start(GTK_BOX(top), ui.time, FALSE, FALSE, 0);

    ui.info = make_label("", 1);
    gtk_box_pack_start(GTK_BOX(top), ui.info, FALSE, FALSE, 0);

    ui.device = make_label("", 1);
    gtk_box_pack_start(GTK_BOX(top), ui.device, FALSE, FALSE, 0);

    ui.status = make_label("", 1);
    gtk_box_pack_start(GTK_BOX(top), ui.status, FALSE, FALSE, 0);

    ui.sep = gtk_separator_new(GTK_ORIENTATION_HORIZONTAL);
    gtk_box_pack_start(GTK_BOX(top), ui.sep, FALSE, FALSE, 6);

    ui.np_box = gtk_box_new(GTK_ORIENTATION_VERTICAL, 4);
    GtkWidget *np_head = make_label("Now playing", 1);
    gtk_style_context_add_class(gtk_widget_get_style_context(np_head), "dimmer");
    gtk_box_pack_start(GTK_BOX(ui.np_box), np_head, FALSE, FALSE, 0);

    GtkWidget *np_card = gtk_box_new(GTK_ORIENTATION_HORIZONTAL, 12);
    gtk_style_context_add_class(gtk_widget_get_style_context(np_card), "np-card");
    ui.np_img = gtk_image_new();
    gtk_widget_set_size_request(ui.np_img, 72, 72);
    gtk_box_pack_start(GTK_BOX(np_card), ui.np_img, FALSE, FALSE, 0);

    GtkWidget *np_text = gtk_box_new(GTK_ORIENTATION_VERTICAL, 2);
    gtk_widget_set_valign(np_text, GTK_ALIGN_CENTER);
    ui.np_title  = make_label("", 0);
    ui.np_artist = make_label("", 1);
    ui.np_status = make_label("", 0);
    gtk_style_context_add_class(gtk_widget_get_style_context(ui.np_artist), "dim");
    gtk_style_context_add_class(gtk_widget_get_style_context(ui.np_status), "np-status");
    gtk_box_pack_start(GTK_BOX(np_text), ui.np_title,  FALSE, FALSE, 0);
    gtk_box_pack_start(GTK_BOX(np_text), ui.np_artist, FALSE, FALSE, 0);
    gtk_box_pack_start(GTK_BOX(np_text), ui.np_status, FALSE, FALSE, 0);
    gtk_box_pack_start(GTK_BOX(np_card), np_text, TRUE, TRUE, 0);
    gtk_box_pack_start(GTK_BOX(ui.np_box), np_card, FALSE, FALSE, 0);
    gtk_widget_show_all(ui.np_box);
    gtk_box_pack_start(GTK_BOX(bot), ui.np_box, FALSE, FALSE, 0);

    GtkWidget *list_head = gtk_box_new(GTK_ORIENTATION_HORIZONTAL, 8);
    ui.list_title = make_label("Your playlists", 1);
    gtk_box_pack_start(GTK_BOX(list_head), ui.list_title, TRUE, TRUE, 0);
    ui.list_btn = gtk_button_new_with_label("Hide list");
    gtk_widget_set_can_focus(ui.list_btn, FALSE);
    gtk_style_context_add_class(gtk_widget_get_style_context(ui.list_btn), "small");
    g_signal_connect(ui.list_btn, "clicked", G_CALLBACK(on_list_btn), NULL);
    gtk_box_pack_start(GTK_BOX(list_head), ui.list_btn, FALSE, FALSE, 0);
    gtk_box_pack_start(GTK_BOX(bot), list_head, FALSE, FALSE, 0);

    ui.store = gtk_list_store_new(2, G_TYPE_STRING, G_TYPE_STRING);
    ui.tracks = gtk_list_store_new(2, G_TYPE_STRING, G_TYPE_STRING);
    ui.queue  = gtk_list_store_new(2, G_TYPE_STRING, G_TYPE_STRING);
    ui.devs   = gtk_list_store_new(4, G_TYPE_STRING, G_TYPE_STRING, G_TYPE_INT, G_TYPE_STRING);
    g_signal_connect(ui.queue, "row-deleted", G_CALLBACK(on_queue_row_deleted), NULL);
    ui.tree = gtk_tree_view_new_with_model(GTK_TREE_MODEL(ui.store));
    gtk_tree_view_set_headers_visible(GTK_TREE_VIEW(ui.tree), FALSE);
    gtk_tree_view_set_enable_search(GTK_TREE_VIEW(ui.tree), FALSE);   /* letters are shortcuts */
    g_signal_connect(ui.tree, "row-activated", G_CALLBACK(on_row_activated), NULL);
    g_signal_connect(ui.tree, "cursor-changed", G_CALLBACK(on_tree_cursor_changed), NULL);

    GtkCellRenderer *cell = gtk_cell_renderer_text_new();
    g_object_set(cell, "ellipsize", PANGO_ELLIPSIZE_END, "ypad", 6, NULL);
    GtkTreeViewColumn *col =
        gtk_tree_view_column_new_with_attributes("Name", cell, "text", 0, NULL);
    gtk_tree_view_append_column(GTK_TREE_VIEW(ui.tree), col);

    GtkWidget *scroll = gtk_scrolled_window_new(NULL, NULL);
    gtk_scrolled_window_set_policy(GTK_SCROLLED_WINDOW(scroll),
                                   GTK_POLICY_NEVER, GTK_POLICY_AUTOMATIC);
    gtk_scrolled_window_set_min_content_height(GTK_SCROLLED_WINDOW(scroll), 90);   /* a few rows always visible */
    gtk_container_add(GTK_CONTAINER(scroll), ui.tree);

    ui.list_rev = gtk_revealer_new();
    gtk_revealer_set_transition_type(GTK_REVEALER(ui.list_rev), GTK_REVEALER_TRANSITION_TYPE_SLIDE_DOWN);
    gtk_revealer_set_transition_duration(GTK_REVEALER(ui.list_rev), 250);
    gtk_revealer_set_reveal_child(GTK_REVEALER(ui.list_rev), TRUE);
    g_signal_connect(ui.list_rev, "notify::child-revealed", G_CALLBACK(on_list_revealed), NULL);
    gtk_container_add(GTK_CONTAINER(ui.list_rev), scroll);
    gtk_box_pack_start(GTK_BOX(bot), ui.list_rev, TRUE, TRUE, 0);

    GtkWidget *btns = gtk_box_new(GTK_ORIENTATION_HORIZONTAL, 8);
    gtk_box_set_homogeneous(GTK_BOX(btns), TRUE);
    gtk_box_pack_start(GTK_BOX(bot), btns, FALSE, FALSE, 0);

    ui.queue_btn = gtk_button_new_with_label("Open queue  (A)");
    gtk_widget_set_can_focus(ui.queue_btn, FALSE);        /* keys keep working */
    g_signal_connect(ui.queue_btn, "clicked", G_CALLBACK(on_queue_btn), NULL);
    gtk_box_pack_start(GTK_BOX(btns), ui.queue_btn, TRUE, TRUE, 0);

    ui.dev_btn = gtk_button_new_with_label("Play on selected device");
    gtk_widget_set_can_focus(ui.dev_btn, FALSE);
    g_signal_connect(ui.dev_btn, "clicked", G_CALLBACK(on_dev_btn), NULL);
    gtk_box_pack_start(GTK_BOX(btns), ui.dev_btn, TRUE, TRUE, 0);

    GtkWidget *mrow = gtk_box_new(GTK_ORIENTATION_HORIZONTAL, 8);
    GtkWidget *mlab = make_label("Floating mini player", 1);
    ui.mini_label = mlab;
    gtk_box_pack_start(GTK_BOX(mrow), mlab, TRUE, TRUE, 0);
    ui.mini_minus = gtk_button_new_with_label("\xE2\x88\x92");       /* minus sign */
    ui.mini_plus  = gtk_button_new_with_label("+");
    gtk_widget_set_can_focus(ui.mini_minus, FALSE);
    gtk_widget_set_can_focus(ui.mini_plus, FALSE);
    gtk_style_context_add_class(gtk_widget_get_style_context(ui.mini_minus), "round");
    gtk_style_context_add_class(gtk_widget_get_style_context(ui.mini_plus), "round");
    gtk_widget_set_tooltip_text(ui.mini_minus, "Close the mini player ( - )");
    gtk_widget_set_tooltip_text(ui.mini_plus, "Open the mini player ( + )");
    g_signal_connect(ui.mini_minus, "clicked", G_CALLBACK(on_mini_minus), NULL);
    g_signal_connect(ui.mini_plus, "clicked", G_CALLBACK(on_mini_plus), NULL);
    gtk_box_pack_start(GTK_BOX(mrow), ui.mini_minus, FALSE, FALSE, 0);
    gtk_box_pack_start(GTK_BOX(mrow), ui.mini_plus, FALSE, FALSE, 0);
    gtk_box_pack_start(GTK_BOX(bot), mrow, FALSE, FALSE, 0);

    GtkWidget *hint = make_label(
        "Space play/pause   Left/Right prev/next   Up/Down choose playlist\n"
        "Enter play playlist   S shuffle   R repeat   F5 reload   Esc quit\n"
        "Q add the highlighted (T list) or middle song to the queue   A open / close queue (or 6 / 7)   + / - open / close the mini player   V devices (play on an idle one)   D play on this PC   Num Lock bring this window forward\n"
        "Click or drag the bar to seek   T list of the highlighted playlist   Scroll / drag the pictures, click one to play   P swap the two playlists   / search songs   H show / hide this help", 1);
    ui.hint = hint;
    gtk_label_set_ellipsize(GTK_LABEL(hint), PANGO_ELLIPSIZE_NONE);
    gtk_label_set_line_wrap(GTK_LABEL(hint), TRUE);
    gtk_box_pack_start(GTK_BOX(bot), hint, FALSE, FALSE, 4);

    gtk_widget_show_all(ui.win);
    gtk_widget_hide(ui.dev_btn);               /* only shown in the device list */
    gtk_widget_hide(ui.np_box);                /* only shown with the queue */
    check_image_support();

    g_timeout_add(500, tick_cb, NULL);

#ifdef _WIN32
    CreateThread(NULL, 0, hook_thread, NULL, 0, NULL);
#endif

    GThread *t = g_thread_new("auth", auth_thread, NULL);
    g_thread_unref(t);

    stall_start();
    stall_beat();
    g_timeout_add(250, beat_cb, NULL);
    gtk_main();
    ui_pool_shutdown();                            /* stop the picture workers before their caches are freed */
    stall_stop();

    activity_log(ACT_SUCCESS, "IMAGE_SUMMARY", -1, NULL, "%d pictures loaded, %d failed this session",
                 g_atomic_int_get(&img_ok), g_atomic_int_get(&img_fail));
    cache_stats_log("CACHE_SUMMARY");
    lru_destroy(thumbs);   thumbs  = NULL;         /* every cache-owned picture / song list is released here */
    lru_destroy(bigs);     bigs    = NULL;
    lru_destroy(plcache);  plcache = NULL;
    activity_log(ACT_SUCCESS, "APP_EXIT", -1, NULL, "Window closed");
    activity_shutdown();                           /* writes everything that is still waiting */
    return 0;
}