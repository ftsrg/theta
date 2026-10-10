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
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
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
    val name = ctx.symbol().original
    val procedure = XcfaProcedureBuilder(name, procedurePassManager)
    val procedureSymbolTable = SvLibSymbolTable(globalSymbolTable)
    xcfaBuilder.addProcedure(procedure)
    procedures[procedure] = procedureSymbolTable

    // input parameters
    ctx.procDeclarationArguments(0).getVars().forEach {
      procedure.addParam(it, ParamDirection.IN)
      procedureSymbolTable.registerVar(it)
    }
    // output parameters
    ctx.procDeclarationArguments(1).getVars().forEach {
      procedure.addParam(it, ParamDirection.OUT)
      procedureSymbolTable.registerVar(it)
    }
    // local variables
    ctx.procDeclarationArguments(2).getVars().forEach {
      procedure.addVar(it)
      procedureSymbolTable.registerVar(it)
    }

    procedure.createInitLoc()
    procedure.createFinalLoc()
    procedure.createErrorLoc()

    val start = newLoc()
    procedure.addEdge(XcfaEdge(procedure.initLoc, start, metadata = EmptyMetaData))
    val statementVisitor = SvLibStatementVisitor(procedure, procedureSymbolTable, charStream, logger)
    statementVisitor.visit(ctx.statement())
    procedure.addEdge(XcfaEdge(statementVisitor.current, procedure.finalLoc.get(), metadata = EmptyMetaData))

    taggedLocations.putAll(statementVisitor.taggedLocations, Set<XcfaLocation>::plus)
  }

  override fun visitVerifyCall(ctx: VerifyCallContext) {
    val name = ctx.symbol().original
    val procedure = procedures.keys.find { it.name == name }
      ?: throw IllegalStateException("No such procedure to verify: $name")

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
              locations.forEach { it.insertCheck(property.relationalTerm().original) }
            }
            else -> warn("Unsupported SV-LIB property: '${property.original}'")
          }
        }
      }
    }
  }

  override fun visitGetWitness(ctx: GetWitnessContext) {
    generateWitness = true
  }

  override fun visitSelectTrace(ctx: SelectTraceContext) = throw ctx.unsupported("command 'select-trace'")

  private fun createGlobalVar(name: String, type: Type) = Decls.Var(name, type).also {
    xcfaBuilder.addVar(XcfaGlobalVar(it))
    globalSymbolTable.registerVar(it)
  }

  private fun XcfaLocation.insertCheck(term: String) = context.let { (procedure, symbolTable) ->
    procedure.insertCheck(this, SvLibTermTransformer(symbolTable).toExpr(term, Bool()))
  }

  private fun ProcDeclarationArgumentsContext.getVars()
    = symbol().zip(sort()).map { (symbol, sort) -> Decls.Var(symbol.original, sortOf(sort)) }

  private val XcfaLocation.context
    get() = procedures.entries.find { (procedure, _) -> this in procedure.getLocs() }?.toPair()
      ?: throw IllegalStateException("Location does not belong to a procedure")
}
