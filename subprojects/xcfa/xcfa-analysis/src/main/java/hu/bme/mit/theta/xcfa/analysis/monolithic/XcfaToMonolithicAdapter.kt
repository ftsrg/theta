/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xcfa.analysis.monolithic

import hu.bme.mit.theta.analysis.algorithm.bounded.pipeline.formalisms.ModelToMonolithicAdapter
import hu.bme.mit.theta.analysis.algorithm.mdd.varordering.Event
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.arraytype.ArrayLitExpr
import hu.bme.mit.theta.core.type.arraytype.ArrayType
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.core.type.fptype.FpType
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.type.rattype.RatExprs.Rat
import hu.bme.mit.theta.core.type.rattype.RatType
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.core.utils.FpUtils
import hu.bme.mit.theta.core.utils.StmtUtils
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cint.CInt
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.analysis.proof.LocationInvariants
import hu.bme.mit.theta.xcfa.model.XCFA
import hu.bme.mit.theta.xcfa.model.optimizeFurther
import hu.bme.mit.theta.xcfa.passes.ProcedurePassManager
import java.math.BigInteger
import org.kframework.mpfr.BigFloat

abstract class XcfaToMonolithicAdapter(
  model: XCFA,
  protected val property: ErrorDetection,
  furtherPasses: ProcedurePassManager,
  protected val parseContext: ParseContext,
  protected val initValues: Boolean,
) : ModelToMonolithicAdapter<XCFA, XcfaState<PtrState<ExplState>>, XcfaAction, LocationInvariants> {

  override val model: XCFA = model.optimizeFurther(furtherPasses)

  protected val intType: Type = CInt.getUnsignedInt(parseContext).smtType

  protected fun smtInt(value: Int): LitExpr<*> =
    when (intType) {
      is IntType -> Int(value)
      is BvType ->
        BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.valueOf(value.toLong()), intType.size)

      else -> error("Unknown integer type: $intType")
    }

  protected fun Stmt.getDefaultValues(excludedVars: Collection<VarDecl<*>>): Expr<BoolType> =
    StmtUtils.getVars(this)
      .filter { it !in excludedVars }
      .map { Eq(it.ref, it.type.defaultValue) }
      .let { And(it) }

  private val Type.defaultValue: LitExpr<out Type>
    get() =
      when (this) {
        is IntType -> smtInt(0)
        is BoolType -> Bool(false)
        is BvType -> BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.ZERO, size)
        is RatType -> Rat(0, 1)
        is FpType -> FpUtils.bigFloatToFpLitExpr(BigFloat.zero(significand), this)
        is ArrayType<*, *> ->
          ArrayLitExpr.of(
            listOf(),
            cast(elemType.defaultValue, elemType),
            ArrayType.of(indexType, elemType),
          )
        else -> error("No default value for type $this")
      }

  protected fun events(stmts: List<Stmt>): List<Event<VarDecl<*>>> =
    stmts
      .map {
        object : Event<VarDecl<*>> {
          override fun getAffectedVars(): List<VarDecl<*>> = StmtUtils.getWrittenVars(it).toList()
        }
      }
      .toList()
}
