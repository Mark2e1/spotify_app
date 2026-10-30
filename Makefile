CFLAGS ?= -Wall -Wextra -O2
LDLIBS  = -lcurl -lcjson -lssl -lcrypto
OBJS    = main.o auth.o player.o util.o

spotify_app: $(OBJS)
	$(CC) $(CFLAGS) -o $@ $(OBJS) $(LDLIBS)

%.o: %.c config.h util.h auth.h player.h
	$(CC) $(CFLAGS) -c $< -o $@

.PHONY: clean
clean:
	rm -f spotify_app $(OBJS)
