#!/bin/sh
set -eu
cd "$(dirname "$0")"
./build.sh
file=$(mktemp)
large=$(mktemp)
missing=$(mktemp)
rm -f "$missing"
trap 'rm -f "$file" "$large" "$missing"' EXIT HUP INT TERM
printf xy > "$file"
printf 'hiZ\177Q\033sq' | timeout --kill-after=2s 10s ./editor "$file" >/dev/null
test "$(cat "$file")" = xQy || { echo 'insert/delete/save failed' >&2; exit 1; }
printf 'iabc\033\023q' | timeout --kill-after=2s 10s ./editor "$missing" >/dev/null
test "$(cat "$missing")" = abc || { echo 'new document was not created' >&2; exit 1; }
printf 'i!\033q' | timeout --kill-after=2s 10s ./editor "$file" >/dev/null
test "$(cat "$file")" = xQy || { echo 'quit must not save' >&2; exit 1; }
if printf s | ./editor >/dev/null; then
    echo 'saving without a path claimed success' >&2; exit 1
else
    test "$?" -eq 3 || exit 1
fi
# Refuse an oversized document rather than saving a truncated prefix over the real file.
head -c 4097 /dev/zero > "$large"
if printf q | ./editor "$large" >/dev/null; then
    echo 'oversized document was accepted' >&2; exit 1
else
    test "$?" -eq 2 || exit 1
fi
test "$(wc -c < "$large")" -eq 4097
printf 'a\nb' > "$large"
if printf q | ./editor "$large" >/dev/null; then
    echo 'multiline document was accepted as one line' >&2; exit 1
else
    test "$?" -eq 2 || exit 1
fi
test "$(wc -c < "$large")" -eq 3
head -c 100 /dev/zero | tr '\000' a > "$large"
rendered=$(printf q | ./editor "$large" | wc -c)
test "$rendered" -eq 78 || { echo 'horizontal viewport did not follow the cursor' >&2; exit 1; }
if test "${1:-}" = --smoke; then
    printf 'PASS: editor relocated build and scripted editing\n'
    exit 0
fi
# The run word's loop must not consume C frames even with optimizer tail calls disabled.
${CC:-cc} -std=c11 -Wall -Wextra -Werror -O0 -fno-inline -fno-optimize-sibling-calls \
    -DWORDLET_NO_FORCED_INLINE -o editor-o0 editor.c host.c
(ulimit -s 256; head -c 20000 /dev/zero | tr '\000' l | timeout --kill-after=2s 20s ./editor-o0 "$file" >/dev/null)
rm -f editor-o0
python3 - <<'PY'
import os, pty, signal, subprocess, termios, time
for exit_action in ('quit', 'signal'):
    master, slave = pty.openpty()
    before = termios.tcgetattr(slave)
    child = subprocess.Popen(['./editor'], stdin=slave, stdout=slave, stderr=subprocess.DEVNULL)
    try:
        for _ in range(100):
            if not termios.tcgetattr(slave)[3] & termios.ICANON:
                break
            time.sleep(0.01)
        else:
            raise AssertionError('raw mode was not entered')
        if exit_action == 'quit':
            os.write(master, b'q')
        else:
            child.send_signal(signal.SIGTERM)
        assert child.wait(timeout=5) == 0
        after = termios.tcgetattr(slave)
        assert before == after, 'terminal settings were not restored after ' + exit_action
    finally:
        if child.poll() is None:
            child.terminate()
            child.wait(timeout=5)
        os.close(master)
        os.close(slave)
PY
printf 'PASS: editor scripted editing, bounded loop, raw-mode restoration\n'
