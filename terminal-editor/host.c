/* The OS boundary for editor.let. Wordlet owns the editing model; C owns POSIX layouts. */
#define _POSIX_C_SOURCE 200809L
#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <termios.h>
#include <unistd.h>
#include <fcntl.h>
#include <signal.h>

uint32_t wordlet_main(void);

static const char *document_path;
static struct termios original_terminal;
static int raw_terminal;
static uint8_t *document_memory;
static volatile sig_atomic_t interrupted;

static void request_exit(int signal_number) {
    (void)signal_number;
    interrupted = 1;
}

uint32_t host_terminal_enter_raw(void) {
    if (!isatty(STDIN_FILENO)) return 0;
    if (tcgetattr(STDIN_FILENO, &original_terminal) != 0) return 0;
    struct termios raw = original_terminal;
    raw.c_iflag &= (tcflag_t)~(BRKINT | ICRNL | INPCK | ISTRIP | IXON);
    raw.c_oflag &= (tcflag_t)~OPOST;
    raw.c_lflag &= (tcflag_t)~(ECHO | ICANON | IEXTEN | ISIG);
    raw.c_cc[VMIN] = 1;
    raw.c_cc[VTIME] = 0;
    if (tcsetattr(STDIN_FILENO, TCSAFLUSH, &raw) != 0) return 0;
    raw_terminal = 1;
    return 1;
}

uint32_t host_terminal_restore(void) {
    if (raw_terminal) {
        (void)tcsetattr(STDIN_FILENO, TCSAFLUSH, &original_terminal);
        raw_terminal = 0;
    }
    return 0;
}

uint8_t *host_document_memory(uint32_t capacity) {
    if (document_memory || !capacity) return NULL;
    document_memory = calloc(capacity, 1);
    return document_memory;
}

uint32_t host_document_load(uint8_t *bytes, uint32_t capacity) {
    if (!document_path || !bytes) return 0;
    int fd = open(document_path, O_RDONLY);
    if (fd < 0) return errno == ENOENT ? 0 : capacity + 1;
    uint32_t length = 0;
    while (length < capacity) {
        ssize_t got = read(fd, bytes + length, capacity - length);
        if (got == 0) break;
        if (got < 0) {
            if (errno == EINTR && !interrupted) continue;
            (void)close(fd);
            return capacity + 1;
        }
        length += (uint32_t)got;
    }
    if (length == capacity) {
        uint8_t extra;
        ssize_t got = read(fd, &extra, 1);
        if (got != 0) length = capacity + 1; /* refuse to save a truncated document */
    }
    (void)close(fd);
    if (length > capacity) return length;
    for (uint32_t i = 0; i < length; ++i) {
        if (bytes[i] < 32 || bytes[i] > 126) return capacity + 1;
    }
    return length;
}

uint32_t host_document_save(uint8_t *bytes, uint32_t length) {
    if (!document_path || !bytes) return 0;
    int fd = open(document_path, O_WRONLY | O_CREAT | O_TRUNC, 0644);
    if (fd < 0) return 0;
    uint32_t written = 0;
    while (written < length) {
        ssize_t n = write(fd, bytes + written, length - written);
        if (n < 0 && errno == EINTR) continue;
        if (n <= 0) break;
        written += (uint32_t)n;
    }
    int ok = written == length && close(fd) == 0;
    if (!ok && written != length) (void)close(fd);
    return ok ? 1u : 0u;
}

uint32_t host_read_byte(uint8_t *out) {
    ssize_t n;
    if (interrupted) return 0;
    do { n = read(STDIN_FILENO, out, 1); } while (n < 0 && errno == EINTR && !interrupted);
    return n == 1 ? 1u : 0u;
}

uint32_t host_terminal_write(uint8_t *bytes, uint32_t length) {
    uint32_t written = 0;
    while (written < length) {
        ssize_t n = write(STDOUT_FILENO, bytes + written, length - written);
        if (n < 0 && errno == EINTR) continue;
        if (n <= 0) break;
        written += (uint32_t)n;
    }
    return written;
}

uint32_t host_terminal_write_range(uint8_t *bytes, uint32_t offset, uint32_t count) {
    return host_terminal_write(bytes + offset, count);
}

uint32_t host_terminal_columns(void) {
    struct winsize size;
    if (ioctl(STDOUT_FILENO, TIOCGWINSZ, &size) != 0 || size.ws_col < 2) return 80;
    return size.ws_col;
}

uint32_t host_terminal_clear(void) {
    static uint8_t clear[] = "\033[H\033[2J";
    return isatty(STDOUT_FILENO) ? host_terminal_write(clear, 7) : 0;
}

uint32_t host_terminal_cursor(uint32_t column) {
    if (isatty(STDOUT_FILENO)) {
        char command[32];
        int n = snprintf(command, sizeof command, "\033[1;%uH", column);
        if (n > 0 && (size_t)n < sizeof command)
            return host_terminal_write((uint8_t *)command, (uint32_t)n);
    }
    return 0;
}

static void release_host(void) {
    (void)host_terminal_restore();
    free(document_memory);
}

int main(int argc, char **argv) {
    document_path = argc > 1 ? argv[1] : NULL;
    if (atexit(release_host) != 0) return 1;
    struct sigaction handler = {0};
    handler.sa_handler = request_exit;
    if (sigemptyset(&handler.sa_mask) != 0
        || sigaction(SIGINT, &handler, NULL) != 0
        || sigaction(SIGTERM, &handler, NULL) != 0
        || sigaction(SIGHUP, &handler, NULL) != 0) return 1;
    return (int)wordlet_main();
}
