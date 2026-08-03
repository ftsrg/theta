# Theta — working notes for Claude

## Launching a full SV-COMP benchmark run (benchcloud)

The run executes on the vcloud via the `benchcloud` SSH host (see `~/.ssh/config`;
zsh on the remote — avoid `===` and other glob-like markers in remote commands).
It takes multiple hours, so it must survive the SSH session: always launch inside
`screen`.

1. **Build the archive** (locally):
   `./gradlew buildArchiveTheta-svcomp -x test`
   → `subprojects/xcfa/xcfa-cli/build/distributions/Theta-svcomp.zip`
   After any rebuild, also `rm -rf subprojects/xcfa/xcfa-cli/build/distributions/Theta-svcomp`
   — stale extracted dirs are silently reused by local tooling (canaries).
2. **Gate on the canaries** before shipping:
   `cd benchmark-results/canaries && ./run_canaries.sh "" parse` must report all PASS.
3. **Upload** to the user's home on benchcloud:
   `scp .../Theta-svcomp.zip benchcloud:Theta-svcomp-new.zip`
4. **Swap in remotely** (delete the old extracted folder, keep names canonical —
   the results path is derived from the tool dir's basename):
   `ssh benchcloud 'rm -rf ~/Theta-svcomp && mv Theta-svcomp-new.zip Theta-svcomp.zip && unzip -q -o Theta-svcomp.zip'`
5. **Launch in screen**:
   `ssh benchcloud 'screen -dmS theta-bench ./run-theta.sh xmls/theta27-short.xml ~/Theta-svcomp'`
   - `run-theta.sh <xml> <tool-dir>` wraps `~/benchexec/contrib/vcloud-benchmark.py`
     and writes results under `results/Theta-svcomp/theta27-short.xml/<timestamp>/`.
   - `run-tool.sh` is the same without the timestamped output dir — prefer `run-theta.sh`.
6. **Check progress** later with `screen -ls` / `screen -r theta-bench` on benchcloud;
   results also land on `sosy:/data/scratch/bajczi/results` (rsync'd).

## Launching on `sosy` (the host actually used since 2026-07-19)

Same idea, different layout — and one trap that fakes a successful run.

- **Working dir is `/data/scratch/bajczi`, not the home dir.** `run-tool.sh`,
  `xmls/theta27-short.xml`, the tool dirs and `results/` all live there.
- Launch in `tmux` (not screen), one session per run:
  `ssh sosy 'cd /data/scratch/bajczi && tmux new-session -d -s theta-bench-NN \
     "cd /data/scratch/bajczi && ./run-tool.sh xmls/theta27-short.xml Theta-svcomp-NN \
      --vcloudCPUModel 5750G > /data/scratch/bajczi/bench-theta27-NN-<ts>.log 2>&1"'`

⚠️ **Always pin the CPU model (`--vcloudCPUModel 5750G`) — no exceptions.** Results get compared
across configs and against runs from weeks earlier; on unpinned runs the jobs land on whatever
vcloud machines happen to be free, so a config difference and a hardware difference become
indistinguishable after the fact and the run is useless as a baseline. Pin it even when the run is
large enough that pinning noticeably slows it down — throughput is the cheaper thing to give up.
(A `<require cpuModel="..."/>` in the XML does the same job, but the launch flag lets one XML be
reused.)

⚠️ **Pass `--vcloudClientHeap <MB>` for anything but a plain full run.** The vcloud client's
default heap is **100 MB** (`benchexec/contrib/vcloud/vcloudbenchmarkbase.py`, grown only by
`numberOfRuns // 10`), and its own help says "A too small heap-size may terminate the client
without any results" — which is exactly what happens: `OutOfMemoryError` in
`BenchmarkRunCollectionBuilder` a few seconds in, **0 submissions, tmux session gone, and a normal
looking benchexec epilogue with all the `.xml.bz2` names printed**. Another
looks-complete-but-worthless failure, same family as the abs-path trap below. `8192` was ample for a
62-run job. Do NOT reach for `JAVA_TOOL_OPTIONS`/`_JAVA_OPTIONS` instead: they make every JVM print
`Picked up JAVA_TOOL_OPTIONS: …`, which pollutes `theta-start.sh --version` output and breaks
benchexec's tool-info with `ValueError: invalid literal for int() with base 10: ''`.

⚠️ **The tool dir MUST be relative** (`Theta-svcomp-NN`), never an absolute path.
`run-tool.sh` runs the job with `--hidden-dir /home --overlay-dir "$PWD"`; with an
absolute path the container cannot resolve `theta-start.sh`, so **every** run dies as
`Cannot start process: [Errno 2] ... theta-start.sh` → `FAILED (KILLED BY SIGNAL 1)`.
The whole 36,602-run benchmark then "finishes" in ~8 minutes, writes all 55
`.xml.bz2` files and prints benchexec's normal completion epilogue — it looks like a
completed run and is entirely worthless. (Hit on 2026-07-20; the failed attempt is
archived at `results/Theta-svcomp-51-FAILED-abspath`.)

**Sanity-check every run before trusting its progress:**
- `grep -c "Cannot start process" <log>` must be **0**.
- Real verdicts (`true` / `false(...)` / `TIMEOUT`) must actually be accumulating.
- `grep -c writeRunResult <log>` counts **submissions, not completions** — it reaches
  36,602 early and is *not* a completion signal on its own.
- Done = 55 `.xml.bz2` in the results dir **and** the tmux session gone (benchexec
  writes the XMLs only at the very end, so never pull while the session is alive).
- A real run takes ~6.5 h; 0 runs with the session alive early on is just the vcloud
  queue, which is normal and should not be acted on.

## Local verification loop

⚠️ **`timeout N ./theta-start.sh …` does NOT kill the verifier.** The script `exec`s nothing — it
launches a child JVM — so the timeout kills the *script* and leaves the JVM orphaned, still holding
the pipe. Any caller reading that pipe (a `$(...)` capture, a `while read` loop) then hangs
**forever**, long after the timeout should have fired, and the run looks stuck rather than timed out.
Kill the JVM itself (`pkill -f 'theta.jar.*<input path>'`) to release it. This is why batched local
suites appear to wedge on one task; it is not the task being slow.

- Fat jar for fast iteration: `./gradlew :theta-xcfa-cli:shadowJar`
  → `subprojects/xcfa/xcfa-cli/build/libs/theta-xcfa-cli-7.3.0-all.jar`.
- Running the jar directly needs `LD_LIBRARY_PATH=<dist>/lib` (legacy Z3) and
  `--smt-home <dist>/solvers`; `theta-start.sh` sets these but hardcodes `-Xmx14210m`.
- Parse-only smoke test: `--svcomp --backend NONE --loglevel RESULT --property <prp> --architecture ILP32|LP64`
  (success marker: `ParsingResult Success`).
- Canary suite details and traps: `benchmark-results/canaries/run_canaries.sh` header
  comment; guard set for known-wrong neighborhoods: `guard_set.tsv`.
- Benchmark triage log: `benchmark-results/PLAN.md` (batch entries, root causes,
  pending decisions).
