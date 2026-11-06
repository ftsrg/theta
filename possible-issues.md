# Possible issues

Suspected bugs and smells found while working on something else. Delete an entry when it is fixed.

## `LDBL_*` macros do not match the modeled `long double`

`frontends/c-frontend/.../stdlib/MacroExprs.kt` gives the `LDBL_*` macros the IEEE double values
(`LDBL_MANT_DIG` 53, `LDBL_MAX` 1.797e+308, ...), while `ArchitectureConfig` models `long double`
as binary128 (113-bit significand, 15-bit exponent). x86 GCC uses the 80-bit extended format, which
matches neither. `LDBL_EPSILON` is also half the double epsilon (the old `DBL_EPSILON` mistake).

Today the floating-point ones carry a C `L` suffix that the value parser rejects, so a program
using them fails in the frontend instead of getting a wrong value. Dropping the suffix without
fixing the values (or the `long double` model) would turn that into a possible wrong verdict.
