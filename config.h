#ifndef CONFIG_H
#define CONFIG_H

/* The client ID is public (PKCE needs no client secret).
   The redirect URI must exactly match the one in your Spotify dashboard. */
#define SPOTIFY_CLIENT_ID     "55b4ff4c4cef4e279077056d3294053c"
#define SPOTIFY_REDIRECT_URI  "http://127.0.0.1:8888/callback"
#define SPOTIFY_CALLBACK_PORT 8888
#define SPOTIFY_SCOPES \
    "user-read-currently-playing user-read-playback-state user-modify-playback-state"

#define TOKEN_FILE "spotify_token.json"

#endif
