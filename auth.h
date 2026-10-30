#ifndef AUTH_H
#define AUTH_H

/* Loads saved tokens and refreshes them; if that fails, runs the browser
   login. Returns 0 on success. */
int auth_init(void);

/* Gets a fresh access token using the saved refresh token. 0 on success. */
int auth_refresh(void);

/* Current access token (valid after auth_init succeeds). */
const char *auth_access_token(void);

#endif
