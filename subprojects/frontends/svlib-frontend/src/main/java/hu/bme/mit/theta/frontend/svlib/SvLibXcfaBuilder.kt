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

import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.frontend.svlib.SvLibUtils.metadata
import hu.bme.mit.theta.frontend.svlib.SvLibUtils.nextLoc
import hu.bme.mit.theta.frontend.svlib.SvLibUtils.sortOf
import hu.bme.mit.theta.frontend.svlib.SvLibUtils.unsupported
import hu.bme.mit.theta.svlib.frontend.dsl.gen.SvLibBaseVisitor
import hu.bme.mit.theta.svlib.frontend.dsl.gen.SvLibParser
import hu.bme.mit.theta.svlib.frontend.dsl.gen.SvLibParser.*
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.ProcedurePassManager
import hu.bme.mit.theta.xcfa.utils.AssignStmtLabel

class SvLibXcfaBuilder(private val procedurePassManager: ProcedurePassManager)
  : SvLibBaseVisitor<Unit>() {

  private val globalVars: MutableMap<String, VarDecl<*>> = LinkedHashMap()
  private var entryProcedureName: String? = null

  private var entryProcedure: XcfaProcedureBuilder? = null

  private var entryArguments = mutableListOf<TermContext>()

  var generateWitness: Boolean = false
    private set

  private val postconditions: MutableList<RelationalTermContext> = ArrayList()
  private val checkTrueByTag: MutableMap<String, MutableList<RelationalTermContext>> = LinkedHashMap()

  private var procedureCount = 0

  fun buildXcfa(parser: SvLibParser): XCFA {
    val script = parser.script()

    collectGlobalsAndEntry(script)

    val xcfaBuilder = XcfaBuilder("SvLibMain")

    for (declaration in globalVars.values) {
      xcfaBuilder.addVar(XcfaGlobalVar(declaration))
    }

    visit(script)

    checkNotNull(entryProcedure) { "SV-LIB input does not define a procedure" }

    xcfaBuilder.addEntryPoint(entryProcedure!!, mutableListOf())

    return xcfaBuilder.build()
  }

  private fun collectGlobalsAndEntry(script: ScriptContext) {
    for (command in script.commandSvLib()) {
      when (command) {
        is DeclareVarContext -> {
          val name = command.symbol().text
          val declaration = Decls.Var(name, sortOf(command.sort()))
          globalVars[name] = declaration
          SvLibUtils.registerVar(declaration, true)
        }
        is SMTLIBv2CommandContext if command.command() is DeclareConstCommandContext -> {
          val cmd = command.command() as DeclareConstCommandContext
          val name = cmd.cmd_declareConst().symbol().text
          val declaration = Decls.Var(name, sortOf(cmd.cmd_declareConst().sort()))
          globalVars[name] = declaration
          SvLibUtils.registerVar(declaration, true)
        }
        is DefineProcContext -> {
          procedureCount++
        }
        is VerifyCallContext -> {
          entryProcedureName = command.symbol().text
          entryArguments = command.term().toMutableList()
        }
        is AnnotateTagContext -> {
          collectAnnotateTagProperties(command.annotateTagCommand())
        }
        is GetWitnessContext -> {
          generateWitness = true
        }
      }
    }
    if (procedureCount > 1) {
      throw UnsupportedOperationException(
        "Multiple procedures are not supported"
      )
    }
  }

  private fun collectAnnotateTagProperties(ctx: AnnotateTagCommandContext) {
    val tag = ctx.symbol().text

    for (attribute in ctx.attributeSvLib()) {
      if (attribute is TagPropertyContext && attribute.property() is EnsuresPropertyContext) {
        postconditions.add((attribute.property() as EnsuresPropertyContext).relationalTerm())
      } else if (attribute is TagPropertyContext && attribute.property() is CheckTruePropertyContext) {
        checkTrueByTag.getOrPut(tag) { mutableListOf() }
          .add((attribute.property() as CheckTruePropertyContext).relationalTerm())
      }
    }
  }

  private fun addParams(
    procedure: XcfaProcedureBuilder,
    ctx: ProcDeclarationArgumentsContext,
    direction: ParamDirection
  ) {
    val symbols = ctx.symbol()
    val sorts = ctx.sort()
    symbols.zip(sorts).forEach { (symbol, sort) ->
      val name = symbol.text
      val param = Decls.Var(name, sortOf(sort))
      procedure.addParam(param, direction)
      SvLibUtils.registerVar(param, false)
    }
  }

  private fun addLocals(procedure: XcfaProcedureBuilder, ctx: ProcDeclarationArgumentsContext) {
    val symbols = ctx.symbol()
    val sorts = ctx.sort()
    symbols.zip(sorts).forEach { (symbol, sort) ->
      val name = symbol.text
      val local = Decls.Var(name, sortOf(sort))
      procedure.addVar(local)
      SvLibUtils.registerVar(local, false)
    }
  }

  override fun visitDefineProc(ctx: DefineProcContext) {
    val name = ctx.symbol().text
    if (entryProcedureName != null && entryProcedureName != name || entryProcedure != null) return

    val procedure = XcfaProcedureBuilder(name, procedurePassManager)

    SvLibUtils.resetSymbolTable()

    addParams(procedure, ctx.procDeclarationArguments(0), ParamDirection.IN)
    addParams(procedure, ctx.procDeclarationArguments(1), ParamDirection.OUT)
    addLocals(procedure, ctx.procDeclarationArguments(2))

    procedure.createInitLoc()
    procedure.createFinalLoc()
    procedure.createErrorLoc()

    val entryLabels = mutableListOf<XcfaLabel>()
    if (entryProcedureName == name) {
      val inputVars = mutableListOf<VarDecl<*>>()

      for (param in procedure.getParams()) {
        if (param.second == ParamDirection.IN) {
          inputVars.add(param.first)
        }
      }

      entryArguments.zip(inputVars).forEach { (arg, param) ->
        entryLabels.add(
          AssignStmtLabel(
            param,
            SvLibUtils.expr(arg, param.getType(), procedure, globalVars),
            metadata(param.name)
          )
        )
      }
    }

    val start = addLabels(procedure, procedure.initLoc, entryLabels)
    val statementVisitor = SvLibStatementVisitor(procedure, globalVars)
    val exit = statementVisitor.visit(ctx.statement(), start)

    applyTaggedCheckTrueProperties(procedure)
    checkTrueByTag.clear()

    if (!statementVisitor.isTerminal(exit))
      addExitEdges(procedure, exit)

    this.entryProcedure = procedure
  }

  override fun visitSelectTrace(ctx: SelectTraceContext) = unsupported("command 'select-trace'")

  private fun applyTaggedCheckTrueProperties(procedure: XcfaProcedureBuilder) {
    if (checkTrueByTag.isEmpty()) return

    for (location in procedure.getLocs().toMutableList()) {
      if (location.metadata !is SvLibMetadata || !(location.metadata as SvLibMetadata).isTag()) continue

      val checkTrueTerms = checkTrueByTag[(location.metadata as SvLibMetadata).tag]
      if (checkTrueTerms.isNullOrEmpty()) continue

      insertChecksBeforeOutgoingEdges(procedure, location, checkTrueTerms)
    }
  }

  private fun insertChecksBeforeOutgoingEdges(
    procedure: XcfaProcedureBuilder,
    source: XcfaLocation,
    checkTrueTerms: List<RelationalTermContext>
  ) {
    val originalOutgoingEdges = source.outgoingEdges.toMutableList()

    var checkedSource = source
    for (checkTrueTerm in checkTrueTerms) {
      val condition = SvLibUtils.relationalBoolExpr(checkTrueTerm, procedure, globalVars)
      val nextCheckedSource = nextLoc("check-true")

      procedure.addEdge(
        XcfaEdge(
          checkedSource,
          procedure.errorLoc.get(),
          StmtLabel(AssumeStmt.of(BoolExprs.Not(condition))),
          EmptyMetaData
        )
      )
      procedure.addEdge(
        XcfaEdge(
          checkedSource,
          nextCheckedSource,
          StmtLabel(AssumeStmt.of(condition)),
          EmptyMetaData
        )
      )

      checkedSource = nextCheckedSource
    }

    for (outgoingEdge in originalOutgoingEdges) {
      procedure.removeEdge(outgoingEdge)
      procedure.addEdge(outgoingEdge.withSource(checkedSource))
    }
  }

  private fun addExitEdges(procedure: XcfaProcedureBuilder, exit: XcfaLocation) {
    var finalSource = exit

    for (postcondition in postconditions) {
      val condition = SvLibUtils.relationalBoolExpr(postcondition, procedure, globalVars)

      procedure.addEdge(
        XcfaEdge(
          finalSource,
          procedure.errorLoc.get(),
          StmtLabel(AssumeStmt.of(BoolExprs.Not(condition))),
          EmptyMetaData
        )
      )

      finalSource =
        addLabels(
          procedure,
          finalSource,
          listOf(StmtLabel(AssumeStmt.of(condition)))
        )
    }

    procedure.addEdge(
      XcfaEdge(
        finalSource,
        procedure.finalLoc.get(),
        NopLabel,
        EmptyMetaData
      )
    )
  }

  private fun addLabels(
    builder: XcfaProcedureBuilder, from: XcfaLocation, labels: List<XcfaLabel>
  ): XcfaLocation {
    if (labels.isEmpty()) return from

    val to = nextLoc("sequence")
    val label = if (labels.size == 1) labels[0] else SequenceLabel(labels)

    builder.addEdge(XcfaEdge(from, to, label, EmptyMetaData))

    return to
  }
}
