#!/usr/bin/env python3
"""Native CLI + real PTY smoke checks, using only public RFC test secrets."""
import argparse
import base64
import errno
import fcntl
import os
from pathlib import Path
import pty
import select
import struct
import subprocess
import termios
import time

ROOT = Path(__file__).resolve().parents[1]
SECRET = "GEZDGNBVGY3TQOJQGEZDGNBVGY3TQOJQ"
TOTP = f"otpauth://totp/RFC?secret={SECRET}&digits=8"
HOTP = f"otpauth://hotp/Fixture?secret={SECRET}&counter=0"


def check_cli(binary):
    result = subprocess.run([binary, "--help"], capture_output=True, timeout=5)
    assert result.returncode == 0 and b"--code-stdin" in result.stdout
    for uri, args, expected in [
        (TOTP, ["--at", "59"], b"94287082\n"),
        (HOTP, [], b"755224\n"),
        (TOTP, ["--at", "20000000000"], b"65353130\n"),
    ]:
        result = subprocess.run([binary, "--code-stdin", *args], input=(uri + "\n").encode(), capture_output=True, timeout=5)
        assert result.returncode == 0 and result.stdout == expected, result
    for text in ["not a URI", TOTP + "\n" + HOTP, "x" * 8193]:
        result = subprocess.run([binary, "--code-stdin"], input=text.encode(), capture_output=True, timeout=5)
        assert result.returncode == 1 and result.stdout == b"" and result.stderr
        assert SECRET.encode() not in result.stderr
    result = subprocess.run([binary, "--code-stdin", "--at", "-1"], input=TOTP.encode(), capture_output=True, timeout=5)
    assert result.returncode == 2
    result = subprocess.run([binary], capture_output=True, timeout=5)
    assert result.returncode == 1 and b"requires a terminal" in result.stderr
    print("PASS: headless codes, invalid input, large timestamps, non-TTY errors")


def check_terminal(binary, quit_key=b"q"):
    master, slave = pty.openpty()
    fcntl.ioctl(slave, termios.TIOCSWINSZ, struct.pack("HHHH", 30, 100, 0, 0))
    original = termios.tcgetattr(slave)

    def controlling_terminal():
        os.setsid()
        fcntl.ioctl(slave, termios.TIOCSCTTY, 0)

    child = subprocess.Popen([binary, "--demo"], stdin=slave, stdout=slave, stderr=slave, preexec_fn=controlling_terminal)
    transcript = bytearray()

    def expect(fragment, send=None, occurrences=1):
        if send is not None:
            os.write(master, send)
        received = bytearray()
        deadline = time.monotonic() + 6
        while time.monotonic() < deadline:
            readable, _, _ = select.select([master], [], [], 0.1)
            if readable:
                try:
                    chunk = os.read(master, 65536)
                except OSError as error:
                    if error.errno == errno.EIO:
                        break
                    raise
                if not chunk:
                    break
                received.extend(chunk)
                transcript.extend(chunk)
                if received.count(fragment) >= occurrences:
                    return
            if child.poll() is not None:
                break
        raise AssertionError(f"terminal did not produce {fragment!r}; output tail={bytes(received[-1200:])!r}")

    try:
        expect(b"755224")
        expect(b"287082", b"\x1b[Fn")
        expect(base64.b64encode(b"287082"), b"c")
        expect(b"Deleted", b"d")
        expect(b"Paste URI (hidden)", b"a")
        expect(b"Invalid otpauth URI", b"\x1b[200~invalid\x1b[201~\r")
        expect(b"Cancelled", b"\x1b")
        expect(b"Paste URI (hidden)", b"a")
        expect(b"Added to this session", b"\x1b[200~" + HOTP.encode() + b"\x1b[201~\r")
        expect(b"Fixture")
        # Wait for two frames with the newly clipped width, so resize is
        # acknowledged before injecting another key sequence. An old frame
        # header already in the PTY buffer cannot acknowledge a resize.
        fcntl.ioctl(slave, termios.TIOCSWINSZ, struct.pack("HHHH", 16, 50, 0, 0))
        expect(b"-" * 49 + b"\r\n", occurrences=4)
        expect(b"OTP TUI", b"\x1b[H\x1b[F")
        # A frame header can already be queued before resize is processed.
        # A fresh clipboard response acknowledges the final navigation event
        # before we test shutdown, rather than racing buffered escape sequences.
        expect(base64.b64encode(b"755224"), b"c")
        os.write(master, quit_key)
        # Keep draining the PTY until exit: otherwise queued redraws can fill
        # its small output buffer before the child reaches the quit event.
        deadline = time.monotonic() + 10
        while child.poll() is None and time.monotonic() < deadline:
            readable, _, _ = select.select([master], [], [], 0.1)
            if readable:
                try:
                    chunk = os.read(master, 65536)
                except OSError as error:
                    if error.errno == errno.EIO:
                        break
                    raise
                transcript.extend(chunk)
        try:
            assert child.wait(timeout=1) == 0
        except subprocess.TimeoutExpired as error:
            raise AssertionError(f"quit was not handled; terminal tail={bytes(transcript[-1000:])!r}") from error
        restored = termios.tcgetattr(slave)
        assert restored == original, "terminal flags were not restored on exit"
        assert SECRET.encode() not in transcript, "URI secret was echoed to the terminal"
        print("PASS: PTY add/delete/copy/HOTP/navigation/resize/hidden URI/terminal restoration", quit_key)
    finally:
        if child.poll() is None:
            child.kill()
            child.wait()
        os.close(master)
        os.close(slave)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("binary", nargs="?", default=str(ROOT / "target/kush/otp_tui"))
    args = parser.parse_args()
    binary = str(Path(args.binary).resolve())
    check_cli(binary)
    check_terminal(binary)
    check_terminal(binary, b"\x03")


if __name__ == "__main__":
    main()
