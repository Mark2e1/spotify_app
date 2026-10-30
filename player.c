#include "player.h"
#include "auth.h"
#include "util.h"

#include <stdio.h>
#include <string.h>

#include <curl/curl.h>
#include <cjson/cJSON.h>

#define API "https://api.spotify.com/v1/me/player"

/* One HTTP request. Returns the HTTP status, or -1 on a network error. */
static long api_once(const char *method, const char *url, Buffer *out) {
    CURL *curl = curl_easy_init();
    if (!curl) return -1;

    char auth[1200];
    snprintf(auth, sizeof auth, "Authorization: Bearer %s", auth_access_token());
    struct curl_slist *headers = curl_slist_append(NULL, auth);

    curl_easy_setopt(curl, CURLOPT_URL, url);
    curl_easy_setopt(curl, CURLOPT_HTTPHEADER, headers);
    curl_easy_setopt(curl, CURLOPT_WRITEFUNCTION, receive_body);
    curl_easy_setopt(curl, CURLOPT_WRITEDATA, out);
    curl_easy_setopt(curl, CURLOPT_TIMEOUT, 30L);
#ifdef _WIN32
    curl_easy_setopt(curl, CURLOPT_SSL_OPTIONS, (long)CURLSSLOPT_NATIVE_CA);
#endif

    if (strcmp(method, "GET") != 0) {
        curl_easy_setopt(curl, CURLOPT_CUSTOMREQUEST, method);
        /* Empty body so curl sends Content-Length: 0 (Spotify requires it). */
        curl_easy_setopt(curl, CURLOPT_POSTFIELDS, "");
    }

    long status = -1;
    CURLcode rc = curl_easy_perform(curl);
    if (rc == CURLE_OK)
        curl_easy_getinfo(curl, CURLINFO_RESPONSE_CODE, &status);
    else
        fprintf(stderr, "Network error: %s\n", curl_easy_strerror(rc));

    curl_slist_free_all(headers);
    curl_easy_cleanup(curl);
    return status;
}

/* Request with one automatic token refresh + retry on HTTP 401.
   Caller must buffer_free(out). */
static long api_call(const char *method, const char *url, Buffer *out) {
    buffer_init(out);
    long status = api_once(method, url, out);

    if (status == 401 && auth_refresh() == 0) {
        buffer_free(out);
        buffer_init(out);
        status = api_once(method, url, out);
    }
    return status;
}

/* Prints a helpful message for failures. Returns 0 if status is 2xx. */
static int check(long status, const Buffer *b) {
    if (status >= 200 && status < 300) return 0;

    switch (status) {
    case -1:
        break; /* network error already reported */
    case 401:
        fprintf(stderr, "Not authorized. Restart the app to log in again.\n");
        break;
    case 403:
        fprintf(stderr,
                "Spotify refused the request (403). Playback control needs "
                "Spotify Premium.\n");
        break;
    case 404:
        fprintf(stderr,
                "No active device. Open Spotify on your phone or computer, "
                "play something, then try again.\n");
        break;
    case 429:
        fprintf(stderr, "Rate limited by Spotify. Wait a moment and retry.\n");
        break;
    default:
        fprintf(stderr, "Spotify returned HTTP %ld: %.200s\n", status,
                b->data ? b->data : "");
    }
    return 1;
}

static int simple_command(const char *method, const char *path,
                          const char *ok_message) {
    char url[256];
    snprintf(url, sizeof url, API "%s", path);

    Buffer b;
    long status = api_call(method, url, &b);
    int rc = check(status, &b);
    buffer_free(&b);

    if (rc == 0) printf("%s\n", ok_message);
    return rc;
}

int player_pause(void) { return simple_command("PUT", "/pause", "Paused."); }
int player_play(void)  { return simple_command("PUT", "/play", "Playing."); }
int player_next(void)  { return simple_command("POST", "/next", "Skipped to next track."); }

static void print_time(const char *label, double ms) {
    long total = (long)(ms / 1000.0);
    printf("%s%ld:%02ld", label, total / 60, total % 60);
}

int player_current(void) {
    Buffer b;
    long status = api_call("GET", API "/currently-playing", &b);

    if (status == 204) {
        printf("Nothing is playing right now.\n");
        buffer_free(&b);
        return 0;
    }
    if (check(status, &b)) {
        buffer_free(&b);
        return 1;
    }

    cJSON *json = b.data ? cJSON_Parse(b.data) : NULL;
    buffer_free(&b);

    cJSON *item = json ? cJSON_GetObjectItemCaseSensitive(json, "item") : NULL;
    if (!cJSON_IsObject(item)) {
        printf("Nothing playing (or this content type isn't supported).\n");
        cJSON_Delete(json);
        return 0;
    }

    cJSON *name = cJSON_GetObjectItemCaseSensitive(item, "name");
    printf("Track  : %s\n", cJSON_IsString(name) ? name->valuestring : "?");

    cJSON *artists = cJSON_GetObjectItemCaseSensitive(item, "artists");
    if (cJSON_IsArray(artists)) {
        printf("Artist : ");
        int first = 1;
        cJSON *artist;
        cJSON_ArrayForEach(artist, artists) {
            cJSON *an = cJSON_GetObjectItemCaseSensitive(artist, "name");
            if (cJSON_IsString(an)) {
                printf("%s%s", first ? "" : ", ", an->valuestring);
                first = 0;
            }
        }
        printf("\n");
    } else {
        cJSON *show = cJSON_GetObjectItemCaseSensitive(item, "show");
        cJSON *sn = show ? cJSON_GetObjectItemCaseSensitive(show, "name") : NULL;
        if (cJSON_IsString(sn)) printf("Show   : %s\n", sn->valuestring);
    }

    cJSON *playing  = cJSON_GetObjectItemCaseSensitive(json, "is_playing");
    cJSON *progress = cJSON_GetObjectItemCaseSensitive(json, "progress_ms");
    cJSON *duration = cJSON_GetObjectItemCaseSensitive(item, "duration_ms");

    printf("Status : %s\n", cJSON_IsTrue(playing) ? "playing" : "paused");
    if (cJSON_IsNumber(progress) && cJSON_IsNumber(duration)) {
        print_time("Time   : ", progress->valuedouble);
        print_time(" / ", duration->valuedouble);
        printf("\n");
    }

    cJSON_Delete(json);
    return 0;
}
