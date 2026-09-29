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

import hu.bme.mit.theta.core.decl.ConstDecl
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.arraytype.ArrayExprs
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.functype.FuncType
import hu.bme.mit.theta.core.type.inttype.IntExprs
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSymbolTable
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibTermTransformer
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibTypeTransformer
import hu.bme.mit.theta.solver.smtlib.solver.model.SmtLibModel
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibTermTransformer
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibTypeTransformer
import hu.bme.mit.theta.svlib.frontend.dsl.gen.SvLibParser
import hu.bme.mit.theta.svlib.frontend.dsl.gen.SvLibParser.OldRelationalTermContext
import hu.bme.mit.theta.svlib.frontend.dsl.gen.SvLibParser.RelationalTermContext
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder
import hu.bme.mit.theta.xcfa.passes.changeVars
import org.antlr.v4.runtime.CharStream
import org.antlr.v4.runtime.ParserRuleContext
import org.antlr.v4.runtime.misc.Interval

object SvLibUtils {

  private var initialSymbolTable = GenericSmtLibSymbolTable()
  private var symbolTable: GenericSmtLibSymbolTable? = null
  private var typeTransformer: SmtLibTypeTransformer = GenericSmtLibTypeTransformer(null)
  private var termTransformer: SmtLibTermTransformer = GenericSmtLibTermTransformer(initialSymbolTable)
  private var charStream: CharStream? = null

  private var locCounter = 0

  fun init(cs: CharStream) {
    initialSymbolTable = GenericSmtLibSymbolTable()
    typeTransformer = GenericSmtLibTypeTransformer(null)
    termTransformer = GenericSmtLibTermTransformer(initialSymbolTable)
    charStream = cs
  }

  fun resetSymbolTable() {
    symbolTable = GenericSmtLibSymbolTable(initialSymbolTable)
    termTransformer = GenericSmtLibTermTransformer(symbolTable)
  }

  fun registerVar(varDecl: VarDecl<*>, initial: Boolean) {
    transformConst(Decls.Const(varDecl.name, varDecl.type), initial)
  }

  fun boolExpr(
    term: SvLibParser.TermContext,
    procedure: XcfaProcedureBuilder,
    declarations: Map<String, VarDecl<*>>
  ) = expr(term, BoolExprs.Bool(), procedure, declarations) as Expr<BoolType>

  fun intExpr(
    term: SvLibParser.TermContext,
    procedure: XcfaProcedureBuilder,
    declarations: Map<String, VarDecl<*>>
  ) = expr(term, IntExprs.Int(), procedure, declarations) as Expr<IntType>

  fun relationalBoolExpr(
    term: RelationalTermContext,
    procedure: XcfaProcedureBuilder,
    declarations: Map<String, VarDecl<*>>
  ) =  relationalExpr(term, BoolExprs.Bool(), procedure, declarations) as Expr<BoolType>

  fun relationalExpr(
    term: RelationalTermContext,
    expectedType: Type,
    procedure: XcfaProcedureBuilder,
    declarations: Map<String, VarDecl<*>>
  )
  = if (term is OldRelationalTermContext) unsupported("relational term 'old'")
    else parseAndReplace(getOriginalText(term), expectedType, procedure, declarations)

  fun expr(
    term: SvLibParser.TermContext,
    expectedType: Type,
    procedure: XcfaProcedureBuilder,
    declarations: Map<String, VarDecl<*>>
  ) = parseAndReplace(getOriginalText(term), expectedType, procedure, declarations)


  private fun parseAndReplace(
    text: String,
    expectedType: Type,
    procedure: XcfaProcedureBuilder,
    declarations: Map<String, VarDecl<*>>
  ): Expr<*> {
    val expr = termTransformer.toExpr(text, expectedType, SmtLibModel(mapOf()))
    val exprVars = ArrayList<ConstDecl<*>>()
    ExprUtils.collectConstants(expr, exprVars)
    val varsToLocal = HashMap<Decl<*>, VarDecl<*>>()

    for (constDecl in exprVars) {
      varsToLocal[constDecl] = resolveVar(constDecl.name, procedure, declarations)
    }

    return expr.changeVars(varsToLocal)
  }

  fun resolveVar(name: String, procedure: XcfaProcedureBuilder, declarations: Map<String, VarDecl<*>>)
    = procedure.getVars().find { it.name == name }
      ?: procedure.getParams().find { (param, _) -> param.name == name }?.first
      ?: declarations[name]
      ?: throw IllegalStateException("Unknown SV-LIB variable '$name'")


  fun getOriginalText(ctx: ParserRuleContext): String
    = charStream!!.getText(Interval(ctx.start.startIndex, ctx.stop.stopIndex))

  fun metadata(sourceName: String) = SvLibMetadata(sourceName)

  fun tagMetadata(tag: String) = SvLibMetadata(tag, tag)

  fun nextLoc(sourceName: String, tag: Boolean = false)
    = XcfaLocation("l" + locCounter++, metadata = if (tag) tagMetadata(sourceName) else metadata(sourceName))

  fun sortOf(sort: SvLibParser.SortContext): Type =
    when (sort) {
      is SvLibParser.SimpleSortContext -> when (sort.identifier().text) {
        "Int" -> IntExprs.Int()
        "Bool" -> BoolExprs.Bool()
        else -> unsupported("sort '${sort.text}'")
      }
      is SvLibParser.ParametricSortContext -> when (sort.identifier().text) {
        "Array" -> {
          val indexType: Type = sortOf(sort.sort(0))
          val elementType: Type = sortOf(sort.sort(1))
          ArrayExprs.Array(indexType, elementType)
        }

        else -> unsupported("sort '${sort.text}'")
      }
      else -> unsupported("sort '${sort.text}'")
    }

  private fun transformConst(decl: ConstDecl<*>, initial: Boolean) {
    val (paramTypes, returnType) = extractTypes(decl.type)

    val returnSort = typeTransformer.toSort(returnType)
    val paramSorts = paramTypes.map(typeTransformer::toSort)

    val symbolName = GenericSmtLibSymbolTable.encodeSymbol(decl.name)
    val symbolDeclaration = "(declare-fun $symbolName (${paramSorts.joinToString(" ")}) $returnSort)"
    (if (initial) initialSymbolTable else symbolTable)!!.put(decl, symbolName, symbolDeclaration)
  }

  private fun extractTypes(type: Type): Pair<List<Type>, Type> {
    if (type is FuncType<*, *>) {
      val paramType = type.getParamType()
      val resultType = type.getResultType()

      check(paramType !is FuncType<*, *>)

      val (paramTypes, newResultType) = extractTypes(resultType)
      val newParamTypes = listOf(paramType) + paramTypes
      return Pair(newParamTypes, newResultType)
    } else {
      return Pair(emptyList(), type)
    }
  }

  fun unsupported(message: String): Nothing
    = throw UnsupportedOperationException("Unsupported SV-LIB element: $message")
}

