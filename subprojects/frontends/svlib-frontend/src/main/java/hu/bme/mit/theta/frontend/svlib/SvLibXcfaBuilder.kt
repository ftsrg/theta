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

import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.arraytype.ArrayExprs
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.bvtype.BvExprs
import hu.bme.mit.theta.core.type.fptype.FpExprs
import hu.bme.mit.theta.core.type.functype.FuncType
import hu.bme.mit.theta.core.type.inttype.IntExprs
import hu.bme.mit.theta.core.type.rattype.RatExprs
import hu.bme.mit.theta.svlib.frontend.dsl.gen.SvLibParser
import hu.bme.mit.theta.svlib.frontend.dsl.gen.SvLibParser.*
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.ProcedurePassManager
import org.antlr.v4.runtime.CharStream

class SvLibXcfaBuilder(private val procedurePassManager: ProcedurePassManager, charStream: CharStream, logger: Logger)
  : SvLibVisitor<Unit>(charStream, logger) {
  private val xcfaBuilder = XcfaBuilder("SvLibMain")
  private val globalSymbolTable = SvLibSymbolTable()
  private val procedures = LinkedHashMap<XcfaProcedureBuilder, SvLibSymbolTable>()
  private val taggedLocations: MutableMap<String, Set<XcfaLocation>> = LinkedHashMap()

  var generateWitness: Boolean = false
    private set

  fun buildXcfa(parser: SvLibParser): XCFA {
    visit(parser.script())
    return xcfaBuilder.build()
  }

  override fun visitDeclareVar(ctx: DeclareVarContext) {
    createGlobalVar(ctx.symbol().original, sortOf(ctx.sort()))
  }

  override fun visitDeclareConstCommand(ctx: DeclareConstCommandContext) {
    val cmd = ctx.cmd_declareConst()
    createGlobalVar(cmd.symbol().original, sortOf(cmd.sort()))
  }

  override fun visitDefineProc(ctx: DefineProcContext) {
    val procedure = declareProcedure(
      ctx.symbol(),
      ctx.procDeclarationArguments(0),
      ctx.procDeclarationArguments(1),
      ctx.procDeclarationArguments(2),
    )
    defineProcedure(procedure, ctx.statement())
  }

  override fun visitDefineProcsRec(ctx: DefineProcsRecContext) {
    val procedures = ctx.procDeclaration().map {
      declareProcedure(
        it.symbol(),
        it.procDeclarationArguments(0),
        it.procDeclarationArguments(1),
        it.procDeclarationArguments(2),
      )
    }
    procedures.zip(ctx.statement()).forEach { (procedure, statement) ->
      defineProcedure(procedure, statement)
    }
  }

  override fun visitVerifyCall(ctx: VerifyCallContext) {
    val name = ctx.symbol().original
    val procedure = procedures.keys.find { it.name == name }
      ?: throw ctx.symbol().illegal("no such procedure '$name'")

    val termTransformer = SvLibTermTransformer(globalSymbolTable)
    val args = procedure.getParams().zip(ctx.term()).map { (param, term) ->
      termTransformer.toExpr(term.original, param.first.type)
    }

    xcfaBuilder.addEntryPoint(procedure, args)
  }

  override fun visitAnnotateTagCommand(ctx: AnnotateTagCommandContext) {
    val tag = ctx.symbol().original
    val locations = taggedLocations[tag] ?: return warn("Annotated tag '$tag' doesn't exist")

    for (attribute in ctx.attributeSvLib().reversed()) {
      when (attribute) {
        is TagAttributeContext -> { // annotating a tag with a tag
          val newTag = attribute.symbol().original
          taggedLocations[newTag] = taggedLocations[tag] ?: emptySet()
        }
        is TagPropertyContext -> {
          when (val property = attribute.property()) {
            is CheckTruePropertyContext -> {
              locations.forEach {
                it.insertCheck(
                  property.relationalTerm().original,
                  SvLibSourceMetadata("${ctx.symbol().original} ${attribute.original}")
                )
              }
            }
            else -> property.unsupported("property '${property.original}'")
          }
        }
      }
    }
  }

  override fun visitGetWitness(ctx: GetWitnessContext) {
    generateWitness = true
  }

  override fun visitSelectTrace(ctx: SelectTraceContext) = throw ctx.unsupported("command 'select-trace'")

  override fun visitDeclareFunCommand(ctx: DeclareFunCommandContext) {
    val sorts = ctx.cmd_declareFun().sort().map { sortOf(it) }
    val type = if (sorts.size == 1) sorts.first()
      else sorts.reduceRight { sort, acc -> FuncType.of(sort, acc) }
    val name = ctx.cmd_declareFun().symbol().original
    globalSymbolTable.put(Decls.Const(name, type), name, ctx.original)
  }

  private fun declareProcedure(
    name: SymbolContext,
    inputs: ProcDeclarationArgumentsContext,
    outputs: ProcDeclarationArgumentsContext,
    locals: ProcDeclarationArgumentsContext,
  ): XcfaProcedureBuilder {
    val procedure = XcfaProcedureBuilder(name.original, procedurePassManager)
    val procedureSymbolTable = SvLibSymbolTable(globalSymbolTable)
    xcfaBuilder.addProcedure(procedure)
    procedures[procedure] = procedureSymbolTable

    inputs.getVars().forEach {
      procedure.addParam(it, ParamDirection.IN)
      procedureSymbolTable.registerVar(it)
    }
    outputs.getVars().forEach {
      procedure.addParam(it, ParamDirection.OUT)
      procedureSymbolTable.registerVar(it)
    }
    locals.getVars().forEach {
      procedure.addVar(it)
      procedureSymbolTable.registerVar(it)
    }

    procedure.createInitLoc()
    procedure.createFinalLoc()
    procedure.createErrorLoc()

    return procedure
  }

  private fun defineProcedure(procedure: XcfaProcedureBuilder, body: StatementContext) {
    val procedureSymbolTable = procedures[procedure] ?: throw body.illegal("no such procedure '${procedure.name}'")
    val statementVisitor = SvLibStatementVisitor(procedure, procedureSymbolTable, charStream, logger)
    statementVisitor.parseProcedureBody(body)
    procedure.addEdge(
      XcfaEdge(statementVisitor.current, procedure.finalLoc.get(), metadata = EmptyMetaData)
    )

    taggedLocations.putAll(statementVisitor.taggedLocations, Set<XcfaLocation>::plus)
  }

  private fun sortOf(sort: SortContext): Type =
    when (sort) {
      is SimpleSortContext -> when (sort.identifier().symbol().original) {
        "Int" -> IntExprs.Int()
        "Bool" -> Bool()
        "Real" -> RatExprs.Rat()
        "FloatingPoint" -> {
          if (sort.identifier().index().size != 2) throw sort.unsupported("sort '${sort.original}'")
          val exponent = sort.identifier().index(0).original.toInt()
          val significand = sort.identifier().index(1).original.toInt()
          FpExprs.FpType(exponent, significand)
        }
        "BitVec" -> {
          if (sort.identifier().index().size != 1) throw sort.unsupported("sort '${sort.original}'")
          val size = sort.identifier().index(0).original.toInt()
          BvExprs.BvType(size)
        }
        else -> throw sort.unsupported("sort '${sort.original}'")
      }
      is ParametricSortContext -> when (sort.identifier().original) {
        "Array" -> {
          val indexType: Type = sortOf(sort.sort(0))
          val elementType: Type = sortOf(sort.sort(1))
          ArrayExprs.Array(indexType, elementType)
        }
        else -> throw sort.unsupported("sort '${sort.original}'")
      }
      else -> throw sort.unsupported("sort '${sort.original}'")
    }

  private fun createGlobalVar(name: String, type: Type) = Decls.Var(name, type).also {
    xcfaBuilder.addVar(XcfaGlobalVar(it))
    globalSymbolTable.registerVar(it)
  }

  private fun XcfaLocation.insertCheck(term: String, metadata: SvLibSourceMetadata) = context.let { (procedure, symbolTable) ->
    procedure.insertCheck(this, SvLibTermTransformer(symbolTable).toExpr(term, Bool()), metadata)
  }

  private fun ProcDeclarationArgumentsContext.getVars()
    = symbol().zip(sort()).map { (symbol, sort) -> Decls.Var(symbol.original, sortOf(sort)) }

  private val XcfaLocation.context
    get() = procedures.entries.find { (procedure, _) -> this in procedure.getLocs() }?.toPair()
      ?: throw IllegalStateException("Location does not belong to a procedure")
}
