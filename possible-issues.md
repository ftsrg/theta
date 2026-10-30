# Possible issues

Suspected bugs and smells found while working on something else. Delete an entry when it is fixed.

- **The synchronization-object flag never reaches the witness writers.** `CLibraryFunctionsPass`
  records `SYNC_VAR_METADATA_KEY` with the handle's `VarDecl` as owner (keyed by identity hash),
  but `YamlWitnessWriter` and `TraceToWitness` look it up by the variable's *name* (keyed by
  `String.hashCode`), so the lookup never matches and non-scalar synchronization objects (e.g. a
  `pthread_mutex_t`) can still appear in `c_expression` constraints.
- **Plain CEGAR crashes on a reference to an array element.** `--backend CEGAR` on a program
  taking `&a[i]` (e.g. the validation set's `own/unsafe.c`) fails with "Undefined default case
  executed for: (ref (deref ... ___idx ...) Int)", in the baseline build as well.
- **`ParsingResult Success` is printed before the XCFA exists.** `getXcfaFromC` (c2xcfa
  `Utils.kt`) prints it right after the ANTLR parse, and `buildFrontend` prints it again at its end.
  The parse-mode canary check looks for the marker, so an exception between the two that is not
  reported as "Frontend failed!" (e.g. in `PrecReuse.load` or `xcfaTraits`) still passes it.
