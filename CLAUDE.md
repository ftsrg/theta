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
