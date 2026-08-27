# core/type — the type-family pattern and its (verified) deviations

Supplements [core's CLAUDE.md](../../../../../../../../../CLAUDE.md) with type-package detail. Everything here was verified against source.

## Canonical pattern — adding to a family

Each `<x>type/` family = `XType` + `XLitExpr` + one class per operator + `XExprs` static factory. To add an operator expr:

1. Copy the nearest sibling. Keep: private ctor, `of(...)` (typed), `create(...)` (wildcard ops, re-typed via `TypeUtils.cast`), per-class `HASH_SEED`, `OPERATOR_LABEL`, lazy `volatile int hashCode`, ops-structural `equals`, `with(...)` returning `this` when ops unchanged.
2. Extend the right arity base (`NullaryExpr`/`UnaryExpr`/`BinaryExpr`/`MultiaryExpr`) — **unless the result type depends on the ops** (see bv deviations below): the bases' `withOps` re-casts new ops to the *old* op types.
3. Register a factory method in `XExprs`.
4. Teach [utils/ExprSimplifier.java](../utils/ExprSimplifier.java): one `addCase(NewExpr.class, this::simplifyNew)` in its `DispatchTable2` + the handler (default = recurse only, no simplification).
5. If it must reach SMT: all four solver stacks (`solver-z3`, `solver-z3-legacy`, `solver-javasmt`, `solver-smtlib`) — `ExprTransformer` at minimum.
6. Pick a **unique** `OPERATOR_LABEL` (check for collisions — toString/DSL round-trips rely on them) and a fresh `HASH_SEED`.

## Trait wiring (abstracttype/)

`AbstractExprs.Add/Eq/Lt/...` do **not** dispatch by `instanceof` on exprs — they call trait methods on the operand's *Type* (`type.Add(ops)`). For a new type to work with them, the `XType` must implement the trait: `Additive`, `Multiplicative`, `Divisible` (Mod/Rem only — Div is in Multiplicative), `Equational`, `Ordered`. Mismatched operand types are reconciled by `AbstractExprs.unify` via `Castable` — implemented **only by `IntType` and `BvType`**.

## Per-family deviations & gotchas

- **bool** — quantifiers live here (`ForallExpr`/`ExistsExpr` extend `QuantifiedExpr`, which implements `Expr<BoolType>` directly to carry `List<ParamDecl<?>>`); their `eval()` throws, and `ExprSimplifier`/`ExprCanonizer` have no quantifier cases. No `BoolEq/NeqExpr`: `IffExpr` *is* the Eq, `XorExpr` *is* the Neq. `SmartBoolExprs` simplifies only `Not`/`Imply`/`And`/`Or`.
- **int** — SMT-LIB **Euclidean** `div`/`mod` (`mod` result in `[0,|divisor|)`); **`rem` takes the divisor's sign** (`5 rem -3 = -2`) — opposite of C/Java `%`. No divide-by-zero guards (unchecked `ArithmeticException`). Literal math lives on `IntLitExpr` itself.
- **rat** — `RatLitExpr` auto-reduces to lowest terms, `denom > 0` (equality relies on this canonical form). `RatType` does *not* implement `Castable`; `RatToIntExpr` is only reachable explicitly (`RatExprs.ToInt`), while Int→Rat also works generically — asymmetric. `RatDivExpr.create` silently promotes bare Int ops to Rat.
- **bv** — `BvType.signed` is a tri-state `Boolean` (`null` = neutral: bitwise ops only; `Div/Mod/Rem/Lt/...` on neutral throw `IllegalStateException`). ⚠ **`BvType.equals` compares only `size`** — signedness is ignored (ops carry their own S/U variants: `SDiv/UDiv`, `SRem/URem`, `SLt/ULt`, ...; `SMod` has no `UMod`). `BvLitExpr` stores `boolean[]` with **index 0 = MSB**; arithmetic round-trips through `BigInteger` via [utils/BvUtils.java](../utils/BvUtils.java). Size-changing exprs (`Concat`/`Extract`/`ZExt`/`SExt`) implement `Expr<BvType>` **directly** (arity bases would mistype them) and hand-roll the boilerplate. `BvSignChangeExpr` (signedness reinterpretation, used by c-frontend) is not in `BvExprs`.
- **fp** — every op with a rounded numeric result (`Add/Sub/Mul/Div/Sqrt/ToBv/ToFp/RoundToIntegral/FromBv`) threads an `FpRoundingMode` (enum RNE/RNA/RTP/RTN/RTZ, default RNE) through ctor + `of`/`create` + `XExprs` + `eval`; comparisons/`IsNan` don't. `eval` computes via MPFR (`BigFloat`, [utils/FpUtils.java](../utils/FpUtils.java)); `roundingMode=null` legitimately means "no rounding needed". ⚠ `FpType.significand` counts the hidden bit; `FpLitExpr`'s stored significand is fraction-only (width −1). `FpAssignExpr` is bit-identity equality (NaN = NaN if same bits); `FpEqExpr` is IEEE `fp.eq` (NaN ≠ everything) — pick deliberately.
- **array** — `ArrayLitExpr` ctor runs `ExprSimplifier` on all ops and `checkState`s they become literals. `ArrayRead/WriteExpr.eval` = linear scan with `elseElem` fallback. `ArrayInitExpr` flattens `[else, indices..., elems...]` into `MultiaryExpr` ops purely for structural equality (documented as non-standard).
- **func** — *not* a lambda calculus: single-param curried apps (`FuncExprs.App` right-folds), `FuncAppExpr.eval()` is an unimplemented TODO stub, `FuncType.getDomainSize()` **throws** (generic domain-size code crashes on it). Main real use: Horn/solver interop (`HornSolver` unwraps `FuncLitExpr` chains).
- **enum** — per-instance type with `literal→ordinal` map; qualified names `Type.Literal` (separator `.`, `makeLongName`/`getShortName`). DSL glue lives in **xsts**, not here.
- **anytype** — `RefExpr` (decl leaf), `IteExpr` (only polymorphic expr with real `eval`), `PrimeExpr` (next-state marker), `Reference`/`Dereference` (pointer-style, memory models; `Dereference` carries an optional uniqueness index). `InvalidLitExpr` = "no valid literal" sentinel; one invalid leaf makes the whole tree `isInvalid()`, and it deliberately doesn't behave as a normal value (don't compare/store it by equality).

## Non-evaluable exprs

`eval()` **throws** on: `ForallExpr`, `ExistsExpr`, `PrimeExpr`, `Reference`, `Dereference`, `FuncAppExpr`. Generic code must not call `eval` on trees that may contain these — they are resolved via solvers/simplification instead.
