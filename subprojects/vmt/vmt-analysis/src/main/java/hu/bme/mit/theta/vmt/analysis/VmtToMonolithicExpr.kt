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
package hu.bme.mit.theta.vmt.analysis

import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.bvtype.BvExprs.BvType
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.rattype.RatExprs.Rat
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.core.utils.TypeUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.solver.javasmt.JavaSMTFormulaConverter
import hu.bme.mit.theta.vmt.VmtModel
import hu.bme.mit.theta.vmt.VmtProperty
import org.sosy_lab.java_smt.api.Formula
import org.sosy_lab.java_smt.api.FormulaType
import org.sosy_lab.java_smt.api.SolverContext

/**
 * Converts a [VmtModel] into a [MonolithicExpr], so the Theta-expression based checkers (BMC,
 * k-induction, IC3, the expression-backed MDD checker) can run on VMT files.
 *
 * Every state variable becomes a variable whose index-0 constant is the current-state symbol and
 * whose index-1 constant is the next-state symbol. Input variables become variables too, with a
 * transition offset of one but no next-state constraint, so each step may pick a new value; other
 * variables can still constrain them. [context] must be the context of the model's formulas.
 */
class VmtToMonolithicExpr
@JvmOverloads
constructor(
  val model: VmtModel,
  context: SolverContext,
  property: VmtProperty? = model.invariantProperties.firstOrNull(),
) {

  /** The Theta variable of each VMT state or input variable, by name. */
  val vars: Map<String, VarDecl<*>>

  val monolithicExpr: MonolithicExpr

  init {
    val fmgr = model.formulaManager
    val converter = JavaSMTFormulaConverter(context)
    val vars = LinkedHashMap<String, VarDecl<*>>()
    for (v in model.stateVars) {
      val decl = Decls.Var(v.name, thetaType(v.type))
      converter.register(decl.getConstDecl(0), v.current)
      converter.register(decl.getConstDecl(1), v.next)
      vars[v.name] = decl
    }
    for (input in model.inputVars) {
      val name = fmgr.extractVariables(input).keys.single()
      val decl = Decls.Var(name, thetaType(fmgr.getFormulaType(input)))
      converter.register(decl.getConstDecl(0), input)
      vars[name] = decl
    }
    this.vars = vars

    fun convert(formula: Formula): Expr<BoolType> =
      PathUtils.foldin(TypeUtils.cast(converter.toExpr(formula), Bool()), 0)

    val prop = property?.formula ?: fmgr.booleanFormulaManager.makeTrue()
    monolithicExpr =
      MonolithicExpr(
        convert(model.init),
        convert(model.trans),
        convert(prop),
        VarIndexingFactory.indexing(1),
        vars.values.toList(),
      )
  }

  private fun thetaType(type: FormulaType<*>): Type =
    when {
      type.isBooleanType -> Bool()
      type.isIntegerType -> Int()
      type.isRationalType -> Rat()
      type.isBitvectorType -> BvType((type as FormulaType.BitvectorType).size)
      else -> throw IllegalArgumentException("Unsupported variable type $type")
    }
}
