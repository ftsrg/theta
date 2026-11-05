/*
 *  Copyright 2026 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.xcfa.passes

import com.google.common.base.Preconditions
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.stmt.Stmts
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.IteExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Imply
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Or
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr
import hu.bme.mit.theta.core.type.fptype.*
import hu.bme.mit.theta.core.type.fptype.FpMathFuncExpr.Function
import hu.bme.mit.theta.core.utils.TypeUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cint.CSignedInt
import hu.bme.mit.theta.xcfa.model.*
import java.util.function.BiFunction

// TODO: type-right conversions (because sqrt and sqrtf might have different domains)
class FpFunctionsToExprsPass(val parseContext: ParseContext) : ProcedurePass {

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    checkNotNull(builder.metaData["deterministic"])
    for (edge in ArrayList(builder.getEdges())) {
      val newStmts: MutableList<XcfaLabel> = ArrayList()
      var found = false
      for (stmt in (edge.label as SequenceLabel).labels) {
        if (stmt is InvokeLabel) {
          if (handlers.containsKey(stmt.name)) {
            when (val label = checkNotNull(handlers[stmt.name]).apply(builder, stmt)) {
              is SequenceLabel -> newStmts.addAll(label.labels)
              else -> newStmts.add(label)
            }
            found = true
          } else newStmts.add(stmt)
        } else newStmts.add(stmt)
      }
      if (found) {
        builder.removeEdge(edge)
        builder.addEdge(XcfaEdge(edge.source, edge.target, SequenceLabel(newStmts), edge.metadata))
      }
    }
    return builder
  }

  private val handlers:
    MutableMap<String, BiFunction<XcfaProcedureBuilder, InvokeLabel, XcfaLabel>> =
    LinkedHashMap()

  private fun addHandler(
    names: Array<String>,
    handler: BiFunction<XcfaProcedureBuilder, InvokeLabel, XcfaLabel>,
  ) {
    for (name in names) {
      handlers[name] = handler
    }
  }

  init {
    addHandler(arrayOf("abs", "labs", "llabs", "imaxabs")) {
      builder: XcfaProcedureBuilder,
      callStmt: InvokeLabel ->
      handleAbs(builder, callStmt)
    }
    addHandler(arrayOf("fabs", "fabsf", "fabsl")) {
      builder: XcfaProcedureBuilder,
      callStmt: InvokeLabel ->
      handleFabs(builder, callStmt)
    }
    addHandler(arrayOf("floor", "floorf", "floorl")) {
      builder: XcfaProcedureBuilder,
      callStmt: InvokeLabel ->
      handleFloor(builder, callStmt)
    }
    addHandler(arrayOf("fmax", "fmaxf", "fmaxl")) {
      builder: XcfaProcedureBuilder,
      callStmt: InvokeLabel ->
      handleFmax(builder, callStmt)
    }
    addHandler(arrayOf("fmin", "fminf", "fminl")) {
      builder: XcfaProcedureBuilder,
      callStmt: InvokeLabel ->
      handleFmin(builder, callStmt)
    }
    addHandler(arrayOf("fmod", "fmodf", "fmodl")) {
      builder: XcfaProcedureBuilder,
      callStmt: InvokeLabel ->
      handleFmod(builder, callStmt)
    }
    addHandler(arrayOf("sqrt", "sqrtf", "sqrtl")) {
      builder: XcfaProcedureBuilder,
      callStmt: InvokeLabel ->
      handleSqrt(builder, callStmt)
    }
    addHandler(arrayOf("round", "roundf", "roundl")) {
      builder: XcfaProcedureBuilder,
      callStmt: InvokeLabel ->
      handleRound(builder, callStmt)
    }
    addHandler(arrayOf("isnan", "__isnan", "isnanf", "__isnanf", "isnanl", "__isnanl")) {
      builder: XcfaProcedureBuilder,
      callStmt: InvokeLabel ->
      handleIsnan(builder, callStmt)
    }
    addHandler(arrayOf("trunc", "truncf", "truncl")) {
      builder: XcfaProcedureBuilder,
      callStmt: InvokeLabel ->
      handleTrunc(builder, callStmt)
    }
    addHandler(arrayOf("ceil", "ceilf", "ceill")) {
      builder: XcfaProcedureBuilder,
      callStmt: InvokeLabel ->
      handleCeil(builder, callStmt)
    }
    addHandler(arrayOf("nan", "nanf", "nanl")) { _, callStmt -> handleNan(callStmt) }
    addHandler(arrayOf("fdim", "fdimf", "fdiml")) { builder, callStmt ->
      handleFdim(builder, callStmt)
    }
    addHandler(arrayOf("remainder", "remainderf", "remainderl")) { builder, callStmt ->
      handleRemainder(builder, callStmt)
    }
    addHandler(arrayOf("modf", "modff", "modfl")) { builder, callStmt ->
      handleModf(builder, callStmt)
    }
    addHandler(arrayOf("copysign", "copysignf", "copysignl")) { builder, callStmt ->
      handleCopysign(builder, callStmt)
    }
    addMathFunc(arrayOf("exp", "expf", "expl"), Function.EXP, ::expFacts)
    addMathFunc(arrayOf("expm1", "expm1f", "expm1l"), Function.EXPM1, ::expm1Facts)
    addMathFunc(arrayOf("log", "logf", "logl"), Function.LOG, ::logFacts)
    addMathFunc(arrayOf("log1p", "log1pf", "log1pl"), Function.LOG1P, ::log1pFacts)
    addMathFunc(arrayOf("sin", "sinf", "sinl"), Function.SIN, ::sinFacts)
    addMathFunc(arrayOf("cos", "cosf", "cosl"), Function.COS, ::cosFacts)
    addMathFunc(arrayOf("tanh", "tanhf", "tanhl"), Function.TANH, ::oddSigmoidFacts)
    addMathFunc(arrayOf("erf", "erff", "erfl"), Function.ERF, ::oddSigmoidFacts)
    addHandler(arrayOf("isnormal")) { builder: XcfaProcedureBuilder, callStmt: InvokeLabel ->
      handleIsnormal(builder, callStmt)
    }
    addHandler(arrayOf("isinf", "__isinf", "__isinff", "isinff", "__isinfl", "isinfl")) {
      builder: XcfaProcedureBuilder,
      callStmt: InvokeLabel ->
      handleIsinf(builder, callStmt)
    }
    addHandler(
      arrayOf(
        "isfinite",
        "finite",
        "isfinitef",
        "finitef",
        "isfinite",
        "finitel",
        "__finite",
        "__finitef",
        "__finitel",
        "__isfinite",
        "__isfinitef",
        "__isfinitel",
      )
    ) { builder: XcfaProcedureBuilder, callStmt: InvokeLabel ->
      handleIsfinite(builder, callStmt)
    }
    addHandler(arrayOf("__fpclassify", "__fpclassifyf", "__fpclassifyl")) {
      builder: XcfaProcedureBuilder,
      callStmt: InvokeLabel ->
      handleFpclassify(builder, callStmt)
    }
    // The C comparison macros (and their GCC builtins) never raise on NaN and yield 0 when an
    // operand is NaN -- which is exactly the IEEE-754 semantics of the SMT FP comparison operators.
    addHandler(arrayOf("isgreater", "__builtin_isgreater")) { _, callStmt ->
      handleFpPredicate(callStmt) { l, r -> FpExprs.Gt(l, r) }
    }
    addHandler(arrayOf("isgreaterequal", "__builtin_isgreaterequal")) { _, callStmt ->
      handleFpPredicate(callStmt) { l, r -> FpExprs.Geq(l, r) }
    }
    addHandler(arrayOf("isless", "__builtin_isless")) { _, callStmt ->
      handleFpPredicate(callStmt) { l, r -> FpExprs.Lt(l, r) }
    }
    addHandler(arrayOf("islessequal", "__builtin_islessequal")) { _, callStmt ->
      handleFpPredicate(callStmt) { l, r -> FpExprs.Leq(l, r) }
    }
    addHandler(arrayOf("islessgreater", "__builtin_islessgreater")) { _, callStmt ->
      handleFpPredicate(callStmt) { l, r -> Or(FpExprs.Lt(l, r), FpExprs.Gt(l, r)) }
    }
    addHandler(arrayOf("isunordered", "__builtin_isunordered")) { _, callStmt ->
      handleFpPredicate(callStmt) { l, r -> Or(FpIsNanExpr.of(l), FpIsNanExpr.of(r)) }
    }
  }

  /**
   * Models a binary floating-point predicate (the C `isgreater`/`isless`/... comparison-macro
   * family) whose result is an int (1 if the predicate holds, 0 otherwise). Both operands are
   * promoted to their smallest common type before comparing.
   */
  private fun handleFpPredicate(
    callStmt: InvokeLabel,
    cmp: (Expr<FpType>, Expr<FpType>) -> Expr<hu.bme.mit.theta.core.type.booltype.BoolType>,
  ): XcfaLabel {
    Preconditions.checkState(callStmt.params.size == 3, "Function is presumed to be binary!")
    val expr = callStmt.params[0]
    Preconditions.checkState(expr is RefExpr<*>)
    if (!parseContext.metadata.getMetadataValue(expr, "cType").isPresent) {
      throw UnsupportedOperationException("Not yet supported without cType")
    }
    val resultType = CComplexType.getType(expr, parseContext)
    val operandType =
      CComplexType.getSmallestCommonType(
        listOf(
          CComplexType.getType(callStmt.params[1], parseContext),
          CComplexType.getType(callStmt.params[2], parseContext),
        ),
        parseContext,
      )
    @Suppress("UNCHECKED_CAST")
    val left =
      TypeUtils.cast(operandType.castTo(callStmt.params[1]), operandType.smtType) as Expr<FpType>
    @Suppress("UNCHECKED_CAST")
    val right =
      TypeUtils.cast(operandType.castTo(callStmt.params[2]), operandType.smtType) as Expr<FpType>
    val assign: AssignStmt<*> =
      Stmts.Assign(
        TypeUtils.cast((expr as RefExpr<*>).decl as VarDecl<*>, resultType.smtType),
        TypeUtils.cast(
          AbstractExprs.Ite<Type>(cmp(left, right), resultType.unitValue, resultType.nullValue),
          resultType.smtType,
        ),
      )
    parseContext.metadata.create(assign.expr, "cType", resultType)
    return StmtLabel(assign, metadata = callStmt.metadata)
  }

  private var tmpCounter = 0

  /** The return slot of a floating-point call and its C type. */
  private fun fpReturn(callStmt: InvokeLabel): Pair<VarDecl<FpType>, CComplexType> {
    val ret = callStmt.params[0]
    Preconditions.checkState(ret is RefExpr<*>)
    val type = CComplexType.getType(ret, parseContext)
    check(type.smtType is FpType) { "${callStmt.name} is presumed to return a floating type" }
    @Suppress("UNCHECKED_CAST")
    return Pair((ret as RefExpr<*>).decl as VarDecl<FpType>, type)
  }

  /**
   * Evaluates the C arguments [indices] (converted to [type]) into fresh variables, so that a
   * multi-statement model reads them once, before it writes anything they may alias.
   */
  private fun freshArgs(
    builder: XcfaProcedureBuilder,
    callStmt: InvokeLabel,
    type: CComplexType,
    vararg indices: Int,
  ): Pair<List<XcfaLabel>, List<Expr<FpType>>> {
    val labels = ArrayList<XcfaLabel>()
    val refs = ArrayList<Expr<FpType>>()
    for (i in indices) {
      val v = Var("__fp_${callStmt.name}_arg_${tmpCounter++}", type.smtType as FpType)
      builder.addVar(v)
      @Suppress("UNCHECKED_CAST")
      val value = TypeUtils.cast(type.castTo(callStmt.params[i]), type.smtType) as Expr<FpType>
      labels.add(StmtLabel(Stmts.Assign(v, value), metadata = callStmt.metadata))
      parseContext.metadata.create(v.ref, "cType", type)
      refs.add(v.ref)
    }
    return Pair(labels, refs)
  }

  private fun assignFp(
    callStmt: InvokeLabel,
    ret: VarDecl<FpType>,
    type: CComplexType,
    rhs: Expr<FpType>,
  ): XcfaLabel {
    val assign = Stmts.Assign(ret, rhs)
    parseContext.metadata.create(assign.expr, "cType", type)
    return StmtLabel(assign, metadata = callStmt.metadata)
  }

  /** The sign bit of a non-NaN value; false for NaN, whose sign the FP theory does not model. */
  private fun isNegative(x: Expr<FpType>): Expr<BoolType> =
    Or(FpExprs.Lt(x, FpExprs.PositiveZero(x.type)), FpExprs.FpAssign(x, FpExprs.NegativeZero(x.type)))

  /** `copysign(mag, sign)` for a non-NaN [sign]. */
  private fun withSignOf(mag: Expr<FpType>, sign: Expr<FpType>): Expr<FpType> =
    IteExpr.of(isNegative(sign), FpExprs.Neg(FpExprs.Abs(mag)), FpExprs.Abs(mag))

  private fun handleNan(callStmt: InvokeLabel): XcfaLabel {
    Preconditions.checkState(callStmt.params.size == 2, "Function is presumed to be unary!")
    val (ret, type) = fpReturn(callStmt)
    return assignFp(callStmt, ret, type, FpExprs.NaN(ret.type))
  }

  /** `fdim(x, y)`: NaN if either is NaN, `x - y` if `x > y`, otherwise `+0`. */
  private fun handleFdim(builder: XcfaProcedureBuilder, callStmt: InvokeLabel): XcfaLabel {
    Preconditions.checkState(callStmt.params.size == 3, "Function is presumed to be binary!")
    val (ret, type) = fpReturn(callStmt)
    val (labels, args) = freshArgs(builder, callStmt, type, 1, 2)
    val (x, y) = args
    val rhs =
      IteExpr.of(
        Or(FpExprs.IsNan(x), FpExprs.IsNan(y)),
        FpExprs.NaN(ret.type),
        IteExpr.of(
          FpExprs.Gt(x, y),
          FpExprs.Sub(FpRoundingMode.RNE, x, y),
          FpExprs.PositiveZero(ret.type),
        ),
      )
    return SequenceLabel(labels + assignFp(callStmt, ret, type, rhs))
  }

  /** C `remainder` is the IEEE-754 remainder (quotient rounded to nearest-even), i.e. `fp.rem`. */
  private fun handleRemainder(builder: XcfaProcedureBuilder, callStmt: InvokeLabel): XcfaLabel {
    Preconditions.checkState(callStmt.params.size == 3, "Function is presumed to be binary!")
    val (ret, type) = fpReturn(callStmt)
    val (labels, args) = freshArgs(builder, callStmt, type, 1, 2)
    return SequenceLabel(labels + assignFp(callStmt, ret, type, FpExprs.Rem(args[0], args[1])))
  }

  /**
   * `modf(x, &ip)`: `ip = trunc(x)` and the result is `x - ip`, which is exact. The fraction takes
   * the sign of `x` (`modf(-3.0)` is `-0.0`, which the subtraction alone gets wrong), and it is
   * `±0` for an infinite `x`.
   */
  private fun handleModf(builder: XcfaProcedureBuilder, callStmt: InvokeLabel): XcfaLabel {
    Preconditions.checkState(callStmt.params.size == 3, "Function is presumed to be binary!")
    val (ret, type) = fpReturn(callStmt)
    val ptr = callStmt.params[2]
    val ptrType = CComplexType.getType(ptr, parseContext)
    check(ptrType is CPointer && ptrType.embeddedType.smtType == type.smtType) {
      "${callStmt.name}: unexpected integral-part pointer type $ptrType"
    }
    val (labels, args) = freshArgs(builder, callStmt, type, 1)
    val x = args[0]
    val ip = FpExprs.RoundToIntegral(FpRoundingMode.RTZ, x)
    val index = CComplexType.getUnsignedLong(parseContext).getValue("0")
    @Suppress("UNCHECKED_CAST")
    val deref =
      Dereference.of(ptr as Expr<Type>, TypeUtils.cast(index, ptr.type) as Expr<Type>, ret.type)
    parseContext.metadata.create(deref, "cType", ptrType)
    val store = StmtLabel(MemoryAssignStmt.create(deref, ip), metadata = callStmt.metadata)
    val frac =
      IteExpr.of(
        FpExprs.IsInfinite(x),
        withSignOf(FpExprs.PositiveZero(ret.type), x),
        withSignOf(FpExprs.Sub(FpRoundingMode.RNE, x, ip), x),
      )
    return SequenceLabel(labels + store + assignFp(callStmt, ret, type, frac))
  }

  /**
   * `copysign(x, y)`. Exact unless `y` is NaN: the FP theory has a single, signless NaN, while a C
   * NaN does carry a sign (`0.0/0.0` is negative on x86). That sign is chosen nondeterministically,
   * which over-approximates the call.
   */
  private fun handleCopysign(builder: XcfaProcedureBuilder, callStmt: InvokeLabel): XcfaLabel {
    Preconditions.checkState(callStmt.params.size == 3, "Function is presumed to be binary!")
    val (ret, type) = fpReturn(callStmt)
    val (labels, args) = freshArgs(builder, callStmt, type, 1, 2)
    val (x, y) = args
    val nanSign = Var("__fp_${callStmt.name}_nansign_${tmpCounter++}", Bool())
    builder.addVar(nanSign)
    builder.setOverApproximation()
    val rhs =
      IteExpr.of(
        FpExprs.IsNan(y),
        IteExpr.of(nanSign.ref, FpExprs.Neg(FpExprs.Abs(x)), FpExprs.Abs(x)),
        withSignOf(x, y),
      )
    return SequenceLabel(
      labels +
        StmtLabel(HavocStmt.of(nanSign), metadata = callStmt.metadata) +
        assignFp(callStmt, ret, type, rhs)
    )
  }

  /**
   * A math function with no counterpart in the FP theory: it becomes an
   * [FpMathFuncExpr], which solvers encode as an uninterpreted function, and its result is
   * constrained by [facts]. Being an over-approximation, it marks the procedure: an Unsafe verdict
   * is then reported as Unknown.
   */
  private fun addMathFunc(
    names: Array<String>,
    function: Function,
    facts: (x: Expr<FpType>, r: Expr<FpType>, one: Expr<FpType>) -> List<Expr<BoolType>>,
  ) {
    addHandler(names) { builder, callStmt ->
      Preconditions.checkState(callStmt.params.size == 2, "Function is presumed to be unary!")
      val (ret, type) = fpReturn(callStmt)
      val (labels, args) = freshArgs(builder, callStmt, type, 1)
      val x = args[0]
      @Suppress("UNCHECKED_CAST")
      val one = TypeUtils.cast(type.unitValue, type.smtType) as Expr<FpType>
      val assumption =
        And(listOf(Imply(FpExprs.IsNan(x), FpExprs.IsNan(ret.ref))) + facts(x, ret.ref, one))
      builder.setOverApproximation()
      SequenceLabel(
        labels +
          assignFp(callStmt, ret, type, FpExprs.MathFunc(function, x)) +
          StmtLabel(Stmts.Assume(assumption), metadata = callStmt.metadata)
      )
    }
  }

  // The facts below only bound a result by representable values (0, ±1, ±inf), which faithful
  // rounding preserves, or fix the special values prescribed by C Annex F (F.10).

  private fun fpEq(a: Expr<FpType>, b: Expr<FpType>) = FpExprs.FpAssign(a, b)

  private fun isFinite(x: Expr<FpType>) = Not(Or(FpExprs.IsNan(x), FpExprs.IsInfinite(x)))

  private fun posInf(x: Expr<FpType>) = FpExprs.PositiveInfinity(x.type)

  private fun negInf(x: Expr<FpType>) = FpExprs.NegativeInfinity(x.type)

  private fun zero(x: Expr<FpType>) = FpExprs.PositiveZero(x.type)

  /** Signed zeros map to themselves (`f(±0) = ±0`). */
  private fun keepsZero(x: Expr<FpType>, r: Expr<FpType>) =
    listOf(
      Imply(fpEq(x, zero(x)), fpEq(r, zero(x))),
      Imply(fpEq(x, FpExprs.NegativeZero(x.type)), fpEq(r, FpExprs.NegativeZero(x.type))),
    )

  /** `x > 0 ⇒ r ≥ 0` and `x < 0 ⇒ r ≤ 0`. */
  private fun keepsSign(x: Expr<FpType>, r: Expr<FpType>) =
    listOf(
      Imply(FpExprs.Gt(x, zero(x)), FpExprs.Geq(r, zero(x))),
      Imply(FpExprs.Lt(x, zero(x)), FpExprs.Leq(r, zero(x))),
    )

  private fun inUnitRange(r: Expr<FpType>, one: Expr<FpType>) =
    And(FpExprs.Geq(r, FpExprs.Neg(one)), FpExprs.Leq(r, one))

  private fun expFacts(x: Expr<FpType>, r: Expr<FpType>, one: Expr<FpType>) =
    listOf(
      Imply(Not(FpExprs.IsNan(x)), FpExprs.Geq(r, zero(x))),
      Imply(FpExprs.Eq(x, zero(x)), fpEq(r, one)),
      Imply(FpExprs.Gt(x, zero(x)), FpExprs.Geq(r, one)),
      Imply(FpExprs.Lt(x, zero(x)), FpExprs.Leq(r, one)),
      Imply(fpEq(x, negInf(x)), fpEq(r, zero(x))),
      Imply(fpEq(x, posInf(x)), fpEq(r, posInf(x))),
    )

  private fun expm1Facts(x: Expr<FpType>, r: Expr<FpType>, one: Expr<FpType>) =
    listOf(
      Imply(Not(FpExprs.IsNan(x)), FpExprs.Geq(r, FpExprs.Neg(one))),
      Imply(fpEq(x, negInf(x)), fpEq(r, FpExprs.Neg(one))),
      Imply(fpEq(x, posInf(x)), fpEq(r, posInf(x))),
    ) + keepsZero(x, r) + keepsSign(x, r)

  private fun logFacts(x: Expr<FpType>, r: Expr<FpType>, one: Expr<FpType>) =
    listOf(
      Imply(FpExprs.Lt(x, zero(x)), FpExprs.IsNan(r)),
      Imply(FpExprs.Eq(x, zero(x)), fpEq(r, negInf(x))),
      Imply(fpEq(x, one), fpEq(r, zero(x))),
      Imply(fpEq(x, posInf(x)), fpEq(r, posInf(x))),
      Imply(And(FpExprs.Gt(x, zero(x)), isFinite(x)), isFinite(r)),
      Imply(And(FpExprs.Gt(x, zero(x)), FpExprs.Lt(x, one)), FpExprs.Leq(r, zero(x))),
      Imply(FpExprs.Gt(x, one), FpExprs.Geq(r, zero(x))),
    )

  private fun log1pFacts(x: Expr<FpType>, r: Expr<FpType>, one: Expr<FpType>) =
    listOf(
      Imply(FpExprs.Lt(x, FpExprs.Neg(one)), FpExprs.IsNan(r)),
      Imply(fpEq(x, FpExprs.Neg(one)), fpEq(r, negInf(x))),
      Imply(fpEq(x, posInf(x)), fpEq(r, posInf(x))),
      Imply(And(FpExprs.Gt(x, FpExprs.Neg(one)), isFinite(x)), isFinite(r)),
      Imply(FpExprs.Gt(x, zero(x)), FpExprs.Geq(r, zero(x))),
      Imply(And(FpExprs.Gt(x, FpExprs.Neg(one)), FpExprs.Lt(x, zero(x))), FpExprs.Leq(r, zero(x))),
    ) + keepsZero(x, r)

  private fun sinFacts(x: Expr<FpType>, r: Expr<FpType>, one: Expr<FpType>) =
    listOf(
      Imply(FpExprs.IsInfinite(x), FpExprs.IsNan(r)),
      Imply(isFinite(x), inUnitRange(r, one)),
    ) + keepsZero(x, r)

  private fun cosFacts(x: Expr<FpType>, r: Expr<FpType>, one: Expr<FpType>) =
    listOf(
      Imply(FpExprs.IsInfinite(x), FpExprs.IsNan(r)),
      Imply(isFinite(x), inUnitRange(r, one)),
      Imply(FpExprs.Eq(x, zero(x)), fpEq(r, one)),
    )

  /** `tanh` and `erf`: odd, increasing, with range [-1, 1] and limits ±1 at ±inf. */
  private fun oddSigmoidFacts(x: Expr<FpType>, r: Expr<FpType>, one: Expr<FpType>) =
    listOf(
      Imply(Not(FpExprs.IsNan(x)), inUnitRange(r, one)),
      Imply(fpEq(x, posInf(x)), fpEq(r, one)),
      Imply(fpEq(x, negInf(x)), fpEq(r, FpExprs.Neg(one))),
    ) + keepsZero(x, r) + keepsSign(x, r)

  private fun handleTrunc(builder: XcfaProcedureBuilder, callStmt: InvokeLabel): XcfaLabel {
    Preconditions.checkState(callStmt.params.size == 2, "Function is presumed to be unary!")
    val expr = callStmt.params[0]
    Preconditions.checkState(expr is RefExpr<*>)
    val assign =
      Stmts.Assign(
        (expr as RefExpr<*>).decl as VarDecl<FpType>,
        FpRoundToIntegralExpr.of(
          FpRoundingMode.RTZ,
          TypeUtils.cast(
            CComplexType.getType(expr, parseContext).castTo(callStmt.params[1]),
            CComplexType.getType(expr, parseContext).smtType,
          ) as Expr<FpType?>,
        ),
      )
    if (parseContext.metadata.getMetadataValue(expr, "cType").isPresent) {
      parseContext.metadata.create(assign.expr, "cType", CComplexType.getType(expr, parseContext))
    }
    return StmtLabel(assign, metadata = callStmt.metadata)
  }

  private fun handleCeil(builder: XcfaProcedureBuilder, callStmt: InvokeLabel): XcfaLabel {
    Preconditions.checkState(callStmt.params.size == 2, "Function is presumed to be unary!")
    val expr = callStmt.params[0]
    Preconditions.checkState(expr is RefExpr<*>)
    val assign =
      Stmts.Assign(
        (expr as RefExpr<*>).decl as VarDecl<FpType>,
        FpRoundToIntegralExpr.of(
          FpRoundingMode.RTP,
          TypeUtils.cast(
            CComplexType.getType(expr, parseContext).castTo(callStmt.params[1]),
            CComplexType.getType(expr, parseContext).smtType,
          ) as Expr<FpType?>,
        ),
      )
    if (parseContext.metadata.getMetadataValue(expr, "cType").isPresent) {
      parseContext.metadata.create(assign.expr, "cType", CComplexType.getType(expr, parseContext))
    }
    return StmtLabel(assign, metadata = callStmt.metadata)
  }

  private fun handleIsinf(builder: XcfaProcedureBuilder, callStmt: InvokeLabel): XcfaLabel {
    Preconditions.checkState(callStmt.params.size == 2, "Function is presumed to be unary!")
    val expr = callStmt.params[0]
    Preconditions.checkState(expr is RefExpr<*>)
    val type = CSignedInt(null, parseContext)
    val assign: AssignStmt<*> =
      Stmts.Assign(
        TypeUtils.cast((expr as RefExpr<*>).decl as VarDecl<*>, type.smtType),
        TypeUtils.cast(
          AbstractExprs.Ite<Type>(
            FpIsInfiniteExpr.of(callStmt.params[1] as Expr<FpType?>),
            type.unitValue,
            type.nullValue,
          ),
          type.smtType,
        ),
      )
    parseContext.metadata.create(assign.expr, "cType", type)
    return StmtLabel(assign, metadata = callStmt.metadata)
  }

  private fun handleIsfinite(builder: XcfaProcedureBuilder, callStmt: InvokeLabel): XcfaLabel {
    Preconditions.checkState(callStmt.params.size == 2, "Function is presumed to be unary!")
    val expr = callStmt.params[0]
    Preconditions.checkState(expr is RefExpr<*>)
    val type = CSignedInt(null, parseContext)
    val assign: AssignStmt<*> =
      Stmts.Assign(
        TypeUtils.cast((expr as RefExpr<*>).decl as VarDecl<*>, type.smtType),
        TypeUtils.cast(
          AbstractExprs.Ite<Type>(
            Or(
              FpIsInfiniteExpr.of(callStmt.params[1] as Expr<FpType?>),
              FpIsNanExpr.of(callStmt.params[1] as Expr<FpType?>),
            ),
            type.nullValue,
            type.unitValue,
          ),
          type.smtType,
        ),
      )
    parseContext.metadata.create(assign.expr, "cType", type)
    return StmtLabel(assign, metadata = callStmt.metadata)
  }

  private fun handleIsnormal(builder: XcfaProcedureBuilder, callStmt: InvokeLabel): XcfaLabel {
    Preconditions.checkState(callStmt.params.size == 2, "Function is presumed to be unary!")
    val type = CSignedInt(null, parseContext)
    val value = callStmt.params[1] as Expr<FpType>
    return assignInt(
      callStmt,
      type,
      AbstractExprs.Ite<Type>(isNormal(value), type.unitValue, type.nullValue),
    )
  }

  /** __fpclassify{,f,l}(x) yields glibc's FP_NAN, FP_INFINITE, FP_ZERO, FP_SUBNORMAL, FP_NORMAL. */
  private fun handleFpclassify(builder: XcfaProcedureBuilder, callStmt: InvokeLabel): XcfaLabel {
    Preconditions.checkState(callStmt.params.size == 2, "Function is presumed to be unary!")
    val type = CSignedInt(null, parseContext)
    val (nan, inf, zero, subnormal, normal) =
      listOf("0", "1", "2", "3", "4").map { type.getValue(it) }
    val value = callStmt.params[1] as Expr<FpType>
    fun pick(e: Expr<*>) = TypeUtils.cast(e, type.smtType) as Expr<Type>
    val result =
      AbstractExprs.Ite<Type>(
        FpExprs.IsNan(value),
        pick(nan),
        AbstractExprs.Ite<Type>(
          FpExprs.IsInfinite(value),
          pick(inf),
          AbstractExprs.Ite<Type>(
            FpExprs.Eq(value, FpExprs.PositiveZero(value.type)),
            pick(zero),
            AbstractExprs.Ite<Type>(isNormal(value), pick(normal), pick(subnormal)),
          ),
        ),
      )
    return assignInt(callStmt, type, result)
  }

  /** Finite, non-zero and at least the smallest normal number in magnitude. */
  private fun isNormal(value: Expr<FpType>): Expr<BoolType> {
    val fpType = value.type
    val exponent = BooleanArray(fpType.exponent)
    exponent[exponent.size - 1] = true
    val minNormal =
      FpExprs.Fp(false, BvLitExpr.of(exponent), BvLitExpr.of(BooleanArray(fpType.significand - 1)))
    return And(
      FpExprs.Geq(FpExprs.Abs(value), minNormal),
      Not(FpExprs.IsInfinite(value)),
      Not(FpExprs.IsNan(value)),
    )
  }

  private fun assignInt(callStmt: InvokeLabel, type: CComplexType, rhs: Expr<*>): XcfaLabel {
    val expr = callStmt.params[0]
    Preconditions.checkState(expr is RefExpr<*>)
    val assign: AssignStmt<*> =
      Stmts.Assign(
        TypeUtils.cast((expr as RefExpr<*>).decl as VarDecl<*>, type.smtType),
        TypeUtils.cast(rhs as Expr<Type>, type.smtType),
      )
    parseContext.metadata.create(assign.expr, "cType", type)
    return StmtLabel(assign, metadata = callStmt.metadata)
  }

  private fun handleIsnan(builder: XcfaProcedureBuilder, callStmt: InvokeLabel): XcfaLabel {
    Preconditions.checkState(callStmt.params.size == 2, "Function is presumed to be unary!")
    val expr = callStmt.params[0]
    Preconditions.checkState(expr is RefExpr<*>)
    if (parseContext.metadata.getMetadataValue(expr, "cType").isPresent) {
      val type = CComplexType.getType(expr, parseContext)
      val assign: AssignStmt<*> =
        Stmts.Assign(
          TypeUtils.cast((expr as RefExpr<*>).decl as VarDecl<*>, type.smtType),
          TypeUtils.cast(
            AbstractExprs.Ite<Type>(
              FpIsNanExpr.of(callStmt.params[1] as Expr<FpType?>),
              type.unitValue,
              type.nullValue,
            ),
            type.smtType,
          ),
        )
      parseContext.metadata.create(assign.expr, "cType", type)
      return StmtLabel(assign, metadata = callStmt.metadata)
    } else {
      throw UnsupportedOperationException("Not yet supported without cType")
    }
  }

  private fun handleRound(builder: XcfaProcedureBuilder, callStmt: InvokeLabel): XcfaLabel {
    Preconditions.checkState(callStmt.params.size == 2, "Function is presumed to be unary!")
    val expr = callStmt.params[0]
    Preconditions.checkState(expr is RefExpr<*>)
    val assign =
      Stmts.Assign(
        (expr as RefExpr<*>).decl as VarDecl<FpType>,
        FpRoundToIntegralExpr.of(
          FpRoundingMode.RNA,
          TypeUtils.cast(
            CComplexType.getType(expr, parseContext).castTo(callStmt.params[1]),
            CComplexType.getType(expr, parseContext).smtType,
          ) as Expr<FpType?>,
        ),
      )
    if (parseContext.metadata.getMetadataValue(expr, "cType").isPresent) {
      parseContext.metadata.create(assign.expr, "cType", CComplexType.getType(expr, parseContext))
    }
    return StmtLabel(assign, metadata = callStmt.metadata)
  }

  private fun handleSqrt(builder: XcfaProcedureBuilder, callStmt: InvokeLabel): XcfaLabel {
    Preconditions.checkState(callStmt.params.size == 2, "Function is presumed to be unary!")
    val expr = callStmt.params[0]
    Preconditions.checkState(expr is RefExpr<*>)
    val assign =
      Stmts.Assign(
        (expr as RefExpr<*>).decl as VarDecl<FpType>,
        FpSqrtExpr.of(
          FpRoundingMode.RNE,
          TypeUtils.cast(
            CComplexType.getType(expr, parseContext).castTo(callStmt.params[1]),
            CComplexType.getType(expr, parseContext).smtType,
          ) as Expr<FpType?>,
        ),
      )
    if (parseContext.metadata.getMetadataValue(expr, "cType").isPresent) {
      parseContext.metadata.create(assign.expr, "cType", CComplexType.getType(expr, parseContext))
    }
    return StmtLabel(assign, metadata = callStmt.metadata)
  }

  private fun handleFmod(builder: XcfaProcedureBuilder, callStmt: InvokeLabel): XcfaLabel {
    throw UnsupportedOperationException("Fmod not yet supported!")
  }

  private fun handleFmin(builder: XcfaProcedureBuilder, callStmt: InvokeLabel): XcfaLabel {
    Preconditions.checkState(callStmt.params.size == 3, "Function is presumed to be binary!")
    val expr = callStmt.params[0]
    Preconditions.checkState(expr is RefExpr<*>)
    val assign =
      Stmts.Assign(
        (expr as RefExpr<*>).decl as VarDecl<FpType>,
        FpMinExpr.of(
          TypeUtils.cast(
            CComplexType.getType(expr, parseContext).castTo(callStmt.params[1]),
            CComplexType.getType(expr, parseContext).smtType,
          ) as Expr<FpType?>,
          TypeUtils.cast(
            CComplexType.getType(expr, parseContext).castTo(callStmt.params[2]),
            CComplexType.getType(expr, parseContext).smtType,
          ) as Expr<FpType?>,
        ),
      )
    if (parseContext.metadata.getMetadataValue(expr, "cType").isPresent) {
      parseContext.metadata.create(assign.expr, "cType", CComplexType.getType(expr, parseContext))
    }
    return StmtLabel(assign, metadata = callStmt.metadata)
  }

  private fun handleFmax(builder: XcfaProcedureBuilder, callStmt: InvokeLabel): XcfaLabel {
    Preconditions.checkState(callStmt.params.size == 3, "Function is presumed to be binary!")
    val expr = callStmt.params[0]
    Preconditions.checkState(expr is RefExpr<*>)
    val assign =
      Stmts.Assign(
        (expr as RefExpr<*>).decl as VarDecl<FpType>,
        FpMaxExpr.of(
          TypeUtils.cast(
            CComplexType.getType(expr, parseContext).castTo(callStmt.params[1]),
            CComplexType.getType(expr, parseContext).smtType,
          ) as Expr<FpType?>,
          TypeUtils.cast(
            CComplexType.getType(expr, parseContext).castTo(callStmt.params[2]),
            CComplexType.getType(expr, parseContext).smtType,
          ) as Expr<FpType?>,
        ),
      )
    if (parseContext.metadata.getMetadataValue(expr, "cType").isPresent) {
      parseContext.metadata.create(assign.expr, "cType", CComplexType.getType(expr, parseContext))
    }
    return StmtLabel(assign, metadata = callStmt.metadata)
  }

  private fun handleFloor(builder: XcfaProcedureBuilder, callStmt: InvokeLabel): XcfaLabel {
    Preconditions.checkState(callStmt.params.size == 2, "Function is presumed to be unary!")
    val expr = callStmt.params[0]
    Preconditions.checkState(expr is RefExpr<*>)
    val assign =
      Stmts.Assign(
        (expr as RefExpr<*>).decl as VarDecl<FpType>,
        FpRoundToIntegralExpr.of(
          FpRoundingMode.RTN,
          TypeUtils.cast(
            CComplexType.getType(expr, parseContext).castTo(callStmt.params[1]),
            CComplexType.getType(expr, parseContext).smtType,
          ) as Expr<FpType?>,
        ),
      )
    if (parseContext.metadata.getMetadataValue(expr, "cType").isPresent) {
      parseContext.metadata.create(assign.expr, "cType", CComplexType.getType(expr, parseContext))
    }
    return StmtLabel(assign, metadata = callStmt.metadata)
  }

  /**
   * The integer `abs` family, which is `x < 0 ? -x : x` exactly.
   *
   * Leaving it unmodelled is not neutral: the call would be havoced, and a guard written in terms
   * of it (`if (abs(x) < K)`) then constrains nothing -- which shows up as a *false* overflow
   * report on code that is careful precisely because it uses `abs` to bound its input.
   *
   * `abs(INT_MIN)` has no representable result, and this model says so: the negation it expands to
   * is exactly the case [bvOverflowCondition] and the integer limit check flag as an overflow.
   */
  private fun handleAbs(builder: XcfaProcedureBuilder, callStmt: InvokeLabel): XcfaLabel {
    Preconditions.checkState(callStmt.params.size == 2, "Function is presumed to be unary!")
    val ret = callStmt.params[0]
    Preconditions.checkState(ret is RefExpr<*>)
    val type = CComplexType.getType(ret, parseContext)
    val arg = type.castTo(callStmt.params[1])
    val negated = AbstractExprs.Neg(arg)
    parseContext.metadata.create(negated, "cType", type)
    val abs = AbstractExprs.Ite<Type>(AbstractExprs.Lt(arg, type.nullValue), negated, arg)
    parseContext.metadata.create(abs, "cType", type)
    val assign =
      Stmts.Assign(
        TypeUtils.cast((ret as RefExpr<*>).decl as VarDecl<*>, type.smtType),
        TypeUtils.cast(abs, type.smtType),
      )
    return StmtLabel(assign, metadata = callStmt.metadata)
  }

  private fun handleFabs(builder: XcfaProcedureBuilder, callStmt: InvokeLabel): XcfaLabel {
    Preconditions.checkState(callStmt.params.size == 2, "Function is presumed to be unary!")
    val expr = callStmt.params[0]
    Preconditions.checkState(expr is RefExpr<*>)
    val assign =
      Stmts.Assign(
        (expr as RefExpr<*>).decl as VarDecl<FpType>,
        FpAbsExpr.of(
          TypeUtils.cast(
            CComplexType.getType(expr, parseContext).castTo(callStmt.params[1]),
            CComplexType.getType(expr, parseContext).smtType,
          ) as Expr<FpType?>
        ),
      )
    if (parseContext.metadata.getMetadataValue(expr, "cType").isPresent) {
      parseContext.metadata.create(assign.expr, "cType", CComplexType.getType(expr, parseContext))
    }
    return StmtLabel(assign, metadata = callStmt.metadata)
  }
}
