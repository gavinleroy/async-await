#!/usr/bin/env python3
"""Live progress display for a fuzz run.

One bar per lane, driven by the eagerly-appended <lang>.jsonl records in the
run's cache directory -- the lanes themselves write only to <lang>.log, so
the fuzzer's stdout is nothing but these bars (plus the final table).

    asyncio    [############------------]  15/30   ETA 2:41   14 ok, 1 unconf

On a TTY the bars redraw in place; when piped, a compact heartbeat line is
printed occasionally instead. Exits nonzero on any mismatch, crash, or dead
lane (a lane that ended without writing its summary).

Usage: progress.py RUN_DIR N LANG...   (the driver invokes this; see
fuzz-parallel.sh, which touches RUN_DIR/.lanes-done when all lanes exit)
"""
import json
import os
import sys
import time

run, n, langs = sys.argv[1], int(sys.argv[2]), sys.argv[3:]
t0 = time.time()
tty = sys.stdout.isatty()
drawn = 0

STATUS_TAGS = (("pass", "ok"), ("unconfirmed", "unconf"), ("mismatch", "MISMATCH"),
               ("runtime-crash", "CRASH"), ("runtime-timeout", "timeout"),
               ("gen-fail", "genfail"))
BAD = ("mismatch", "runtime-crash")


def lane_state(lang):
    done, counts = 0, {}
    try:
        with open(os.path.join(run, f"{lang}.jsonl")) as f:
            for line in f:
                try:
                    rec = json.loads(line)
                except json.JSONDecodeError:
                    continue  # partially-written trailing line
                done += 1
                s = rec.get("status", "?")
                counts[s] = counts.get(s, 0) + 1
    except FileNotFoundError:
        pass
    return done, counts


def summary_path(lang):
    return os.path.join(run, f"{lang}-summary.json")


def mmss(sec):
    return f"{int(sec // 60)}:{int(sec % 60):02d}"


def bar(done, total, width=24):
    fill = int(width * min(done, total) / total) if total else width
    return "#" * fill + "-" * (width - fill)


def lane_line(lang):
    done, counts = lane_state(lang)
    parts = [f"{counts[k]} {tag}" for k, tag in STATUS_TAGS if counts.get(k)]
    status = ", ".join(parts) or "starting"
    elapsed = time.time() - t0
    if os.path.exists(summary_path(lang)):
        try:
            wall = json.load(open(summary_path(lang))).get("wall-ms", 0) / 1000
        except (json.JSONDecodeError, OSError):
            wall = elapsed
        tail = f"done {mmss(wall)}"
    elif done == 0:
        tail = "ETA --:--"
    else:
        tail = f"ETA {mmss(elapsed / done * (n - done))}"
    return f"{lang:<11}[{bar(done, n)}] {done:>3}/{n}  {tail:>10}  {status}"


def render():
    global drawn
    lines = [lane_line(l) for l in langs]
    if drawn:
        sys.stdout.write(f"\x1b[{drawn}A")
    for l in lines:
        sys.stdout.write("\r\x1b[2K" + l + "\n")
    drawn = len(lines)
    sys.stdout.flush()


last_heartbeat = 0.0
while True:
    all_summaries = all(os.path.exists(summary_path(l)) for l in langs)
    lanes_dead = os.path.exists(os.path.join(run, ".lanes-done"))
    if tty:
        render()
    elif time.time() - last_heartbeat > 15:
        states = "  ".join(f"{l} {lane_state(l)[0]}/{n}" for l in langs)
        print(f"progress: {states}", flush=True)
        last_heartbeat = time.time()
    if all_summaries or lanes_dead:
        break
    time.sleep(0.5 if tty else 2)

# Final render (also covers the piped case) and summary table.
if tty:
    render()
else:
    for l in langs:
        print(lane_line(l))

total = {"pass": 0, "mismatch": 0, "unconfirmed": 0, "runtime-crash": 0}
dead_lane = False
print()
print(f"{'lane':<11} {'pass':>5} {'mism':>5} {'unconf':>6} {'crash':>5} {'wall':>8}")
for lang in langs:
    p = summary_path(lang)
    if not os.path.exists(p):
        print(f"{lang:<11} LANE DIED -- see {lang}.log")
        dead_lane = True
        continue
    s = json.load(open(p))
    for k in total:
        total[k] += s.get(k, 0)
    print(f"{lang:<11} {s['pass']:>5} {s['mismatch']:>5} {s['unconfirmed']:>6} "
          f"{s['runtime-crash']:>5} {s.get('wall-ms', 0) / 60000:>7.1f}m")
t = total
print(f"{'total':<11} {t['pass']:>5} {t['mismatch']:>5} {t['unconfirmed']:>6} {t['runtime-crash']:>5}")
for lang in langs:
    _, counts = lane_state(lang)
    if any(counts.get(k) for k in BAD):
        print(f"  {lang}: failure details in {os.path.join(run, lang + '.log')}")
sys.exit(1 if (dead_lane or t["mismatch"] or t["runtime-crash"]) else 0)
