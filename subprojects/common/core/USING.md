# Using theta-core from other modules — API cookbook

Consumer-facing counterpart of [CLAUDE.md](CLAUDE.md) (which covers *extending* core). Read this when you build or manipulate exprs/stmts/valuations from any other module.

## Depend on it

```kotlin
// build.gradle.kts
implementation(project(":theta-core"))
```

## Build expressions

The idiom is static-importing the per-family factories:

```java
import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.*;   // Int, Add, Eq, Lt, ...
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.*; // Bool, And, Not, ...

VarDecl<IntType> x = Var("x", Int());          // keep this instance!
Expr<BoolType> phi = And(Lt(x.getRef(), Int(5)), Eq(x.getRef(), Int(3)));
```

- **Keep `Decl` instances.** Equality is identity — `Var("x", Int())` twice = two unrelated variables; there is no name-based lookup.
- `x.getRef()` turns a decl into an expr; type-generic construction (ops of unknown family) goes through `abstracttype/AbstractExprs` (`AbstractExprs.Eq`, `.Add`, ...).
- `SmartBoolExprs` variants simplify while constructing (`And([x])` → `x`); plain `BoolExprs` builds verbatim.
- Simple types are singletons: `Int()`, `Bool()`, `Rat()`. Parametric ones are built per instance: `BvType.of(32)`, `FpType.of(8, 24)`, `ArrayType.of(idxType, elemType)`.

## Evaluate / inspect / transform

```java
LitExpr<BoolType> v = phi.eval(valuation);
// ⚠ throws NoSuchElementException if valuation lacks a referenced decl —
//   for partial evaluation use ExprUtils.simplify(expr, valuation) instead
// ⚠ eval() also THROWS on: Forall/Exists, PrimeExpr, Reference/Dereference,
//   FuncAppExpr — don't eval trees that may contain these
```

Semantics worth knowing (all verified):
- Int `div`/`mod` are SMT-LIB **Euclidean** (`mod` result always in `[0,|divisor|)`); `rem` takes the **divisor's** sign — both differ from C/Java `%`. No division-by-zero guards.
- `BvType.equals` ignores signedness (it's a tri-state `Boolean` attribute; ops carry their own S/U variants). Two `BvType`s of equal size are `.equals()`.
- `SmartBoolExprs` simplifies only `Not`/`Imply`/`And`/`Or` — `Iff`/`Xor`/quantifiers have no smart variants.

[`ExprUtils`](src/main/java/hu/bme/mit/theta/core/utils/ExprUtils.java) is the workhorse (all static): `getVars`, `getAtoms`, `getConjuncts`, `simplify(expr[, valuation])`, `canonize`, `eliminateIte`, `toDnf`, `transformEquiSatCnf`, `getIndexedConstants`, ...

Substitute decls with exprs:

```java
Substitution sub = BasicSubstitution.builder().put(x, Int(1)).build();
Expr<BoolType> phi2 = sub.apply(phi);
```

Valuations: `MutableValuation().put(x, Int(1))`, `ImmutableValuation.builder()...build()`, `ImmutableValuation.empty()`. `Valuation.toExpr()` gives the `x = 1 ∧ ...` conjunction; a `Valuation` *is* a `Substitution`.

## Parsing from text

`CoreDslManager` (in `dsl/`) round-trips types/exprs/atomic stmts: `manager.declare(x); manager.parseStmt("x := x + 1")`. Only `assign`/`assume`/`havoc` stmts are grammar-supported — composite stmts (Sequence/NonDet/If/Loop/…) are Java-API-only.

## Statements

[`StmtUtils`](src/main/java/hu/bme/mit/theta/core/utils/StmtUtils.java): `getVars`, `getWrittenVars`, `toExpr(stmt, indexing)` → `StmtUnfoldResult` (exprs + resulting indexing).

## Talking to a solver

Solvers accept constants only, never `VarDecl`s. Round-trip via [`PathUtils`](src/main/java/hu/bme/mit/theta/core/utils/PathUtils.java) + `VarIndexing` ([utils/indexings/](src/main/java/hu/bme/mit/theta/core/utils/indexings/)):

```java
solver.add(PathUtils.unfold(phi, 0));          // x → _x:0 (IndexedConstDecl)
if (solver.check().isSat()) {
    Valuation model = solver.getModel();
    Valuation vals = PathUtils.extractValuation(model, 0);  // _x:0 → x
}
```

Multi-step paths use one index per step; `VarIndexing` tracks per-var indices (primed exprs bump them, see `StmtUtils.toExpr` / `PrimeExpr`).
