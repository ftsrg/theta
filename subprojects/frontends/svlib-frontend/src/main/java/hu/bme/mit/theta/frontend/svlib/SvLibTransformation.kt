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
package hu.bme.mit.theta.frontend.svlib

import com.google.common.collect.BiMap
import com.google.common.collect.HashBiMap
import hu.bme.mit.theta.core.decl.ConstDecl
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.functype.FuncType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSymbolTable
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibTermTransformer
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibTransformationManager
import hu.bme.mit.theta.solver.smtlib.solver.model.SmtLibModel
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibTermTransformer
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibTransformationManager
import hu.bme.mit.theta.xcfa.passes.changeVars

class SvLibTermTransformer(private val symbolTable: SvLibSymbolTable = SvLibSymbolTable()) {
  private var termTransformer: SmtLibTermTransformer = GenericSmtLibTermTransformer(symbolTable)

  fun <T : Type> toExpr(term: String, type: T): Expr<T> =
    termTransformer
      .toExpr(term, type, SmtLibModel(mapOf()))
      .changeVars(symbolTable.constToVar)
}

class SvLibExprTransformer {
  private val symbolTable = SvLibSymbolTable()
  private val transformationManager: SmtLibTransformationManager = GenericSmtLibTransformationManager(symbolTable)

  fun toTerm(expr: Expr<BoolType>): String {
    ExprUtils.getVars(expr).forEach(symbolTable::registerVar)
    val constExpr = ExprUtils.changeDecls(expr, symbolTable.varToConst)
    return transformationManager.toTerm(constExpr)
  }
}

class SvLibSymbolTable : GenericSmtLibSymbolTable  {
  private val transformationManager: SmtLibTransformationManager = GenericSmtLibTransformationManager(this)
  private val varConstants: BiMap<VarDecl<*>, ConstDecl<*>> = HashBiMap.create()

  constructor() : super()

  constructor(other: SvLibSymbolTable) : super(GenericSmtLibSymbolTable(other)) {
    this.varConstants.putAll(other.varConstants)
  }

  val varToConst: Map<VarDecl<*>, ConstDecl<*>> = varConstants
  val constToVar: Map<ConstDecl<*>, VarDecl<*>> = varConstants.inverse()

  fun registerVar(varDecl: VarDecl<*>) {
    if (varConstants.contains(varDecl)) return

    val constDecl = Decls.Const(varDecl.name, varDecl.type)
    transformConst(constDecl)
    varConstants.putIfAbsent(varDecl, constDecl)
  }

  fun getVar(symbol: String) = constToVar[getConst(symbol)]
    ?: throw IllegalStateException("Unknown SV-LIB variable '$symbol'")

  override fun put(constDecl: ConstDecl<*>, symbol: String, declaration: String) {
    constToSymbol[constDecl] = symbol
    constToDeclaration[constDecl] = declaration
  }

  private fun transformConst(decl: ConstDecl<*>) {
    val (paramTypes, returnType) = this.extractTypes(decl.type)

    val returnSort = transformationManager.toSort(returnType)
    val paramSorts = paramTypes.map(transformationManager::toSort)

    val symbolName = encodeSymbol(decl.name)
    val symbolDeclaration = "(declare-fun $symbolName (${paramSorts.joinToString(" ")}) $returnSort)"
    put(decl, symbolName, symbolDeclaration)
  }

  private fun extractTypes(type: Type): Pair<List<Type>, Type> {
    if (type is FuncType<*, *>) {
      val paramType = type.getParamType()
      val resultType = type.getResultType()

      check(paramType !is FuncType<*, *>)

      val (paramTypes, newResultType) = this.extractTypes(resultType)
      val newParamTypes = listOf(paramType) + paramTypes
      return Pair(newParamTypes, newResultType)
    } else {
      return Pair(emptyList(), type)
    }
  }
}
