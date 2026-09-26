# Possible issues

Suspected bugs and smells found while working on something else. Delete an entry when it is fixed.

- **`--datarace-to-reachability` fails in the frontend on programs calling `memset` (and similar).**
  `DataRaceToReachabilityPass` runs in `CPasses` before `MemoryFunctionsPass` lowers the `mem*`
  calls, and `getMultipleThreadsPerProcedure` (`xcfa/utils/DataRaceUtils.kt`) throws
  `Unknown procedure: memset(...)` for any invoke that is neither a defined procedure nor marked
  `isLibraryFunction`. The portfolio is not affected (it applies the pass to the finished XCFA), but a
  direct `--backend OC --datarace-to-reachability` run reports `ERROR (frontend failed)`, e.g. on
  `pthread/bigshot_p.i`.
