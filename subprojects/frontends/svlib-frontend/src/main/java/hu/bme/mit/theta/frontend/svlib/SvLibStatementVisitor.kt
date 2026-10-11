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
import hu.bme.mit.theta.core.stmt.Stmts
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.svlib.frontend.dsl.gen.SvLibParser.*
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.AssignStmtLabel
import org.antlr.v4.runtime.CharStream
import org.antlr.v4.runtime.ParserRuleContext

class SvLibStatementVisitor(
  private val procedure: XcfaProcedureBuilder,
  private val symbolTable: SvLibSymbolTable,
  charStream: CharStream,
  logger: Logger,
) : SvLibVisitor<Unit>(charStream, logger) {
  private val termTransformer = SvLibTermTransformer(symbolTable)
  var current: XcfaLocation = procedure.initLoc
    private set
  val taggedLocations: MutableMap<String, MutableSet<XcfaLocation>> = LinkedHashMap()
  val labeledLocations: MutableMap<String, XcfaLocation> = LinkedHashMap()
  val gotos: MutableMap<XcfaEdge, String> = LinkedHashMap()
  private val loops = ArrayDeque<Loop>()

  fun parseProcedureBody(ctx: StatementContext) {
    visit(ctx)
    applyGotos()
  }

  override fun visitAssumeStatement(ctx: AssumeStatementContext) {
    val condition = termTransformer.toExpr(ctx.term().original, Bool())
    current = current.extend(StmtLabel(Stmts.Assume(condition), metadata = ctx.metadata))
  }

  override fun visitAssignStatement(ctx: AssignStatementContext) {
    val vars = ctx.symbol().map { symbolTable.getVar(it.original) }
    val exprs = vars.zip(ctx.term()).map { (varDecl, term) ->
      termTransformer.toExpr(term.original, varDecl.getType())
    }

    val label = if (vars.size == 1) {
      AssignStmtLabel(vars.first(), exprs.first(), metadata = ctx.metadata)
    } else {
      val tempVars = vars.filter { varDecl -> exprs.any { varDecl in ExprUtils.getVars(it) } }.associateWith { it.createTemp() }
      tempVars.values.forEach(procedure::addVar)

      val assignments = vars.zip(exprs).map { (varDecl, expr) ->
        AssignStmtLabel(tempVars[varDecl] ?: varDecl, expr, metadata = ctx.metadata)
      }
      val tempAssignments = tempVars.map { (varDecl, tempVar) ->
        AssignStmtLabel(varDecl, tempVar.ref, metadata = ctx.metadata)
      }
      SequenceLabel(assignments + tempAssignments, metadata = ctx.metadata)
    }

    current = current.extend(label)
  }

  override fun visitHavocStatement(ctx: HavocStatementContext) {
    val labels = ctx.symbol().map { symbol ->
      val variable = symbolTable.getVar(symbol.original)
      StmtLabel(Stmts.Havoc(variable), metadata = ctx.metadata)
    }
    val label = if (labels.size == 1) labels.first() else SequenceLabel(labels, metadata = ctx.metadata)

    current = current.extend(label)
  }

  override fun visitSequenceStatement(ctx: SequenceStatementContext) = ctx.statement().forEach(::visit)

  override fun visitIfStatement(ctx: IfStatementContext) {
    val condition = termTransformer.toExpr(ctx.term().original, Bool())
    val ifStart = current
    val ifEnd = newLoc()

    current = ifStart.extend(StmtLabel(Stmts.Assume(condition), metadata = ctx.term().metadata))
    visit(ctx.statement(0))
    procedure.addEdge(XcfaEdge(current, ifEnd, NopLabel, EmptyMetaData))

    current = ifStart.extend(StmtLabel(Stmts.Assume(Not(condition)), metadata = ctx.term().metadata))
    if (ctx.statement().size > 1) visit(ctx.statement(1))
    procedure.addEdge(XcfaEdge(current, ifEnd, NopLabel, EmptyMetaData))

    current = ifEnd
  }

  override fun visitWhileStatement(ctx: WhileStatementContext) {
    val condition = termTransformer.toExpr(ctx.term().original, Bool())
    val loopHead = current
    val loopExit = loopHead.extend(StmtLabel(Stmts.Assume(Not(condition)), metadata = ctx.term().metadata))

    loops.push(Loop(loopHead, loopExit))
    current = loopHead.extend(StmtLabel(Stmts.Assume(condition), metadata = ctx.term().metadata))
    visit(ctx.statement())
    procedure.addEdge(XcfaEdge(current, loopHead, NopLabel, EmptyMetaData))
    loops.pop()

    current = loopExit
  }

  override fun visitContinueStatement(ctx: ContinueStatementContext) {
    if (loops.isEmpty()) throw ctx.illegal("continue outside while")

    procedure.addEdge(
      XcfaEdge(current, loops.peak().head, NopLabel, ctx.metadata)
    )

    current = newLoc()
  }

  override fun visitBreakStatement(ctx: BreakStatementContext) {
    if (loops.isEmpty()) throw ctx.illegal("break outside while")

    procedure.addEdge(
      XcfaEdge(current, loops.peak().exit, NopLabel, ctx.metadata)
    )

    current = newLoc()
  }

  override fun visitCallStatement(ctx: CallStatementContext) {
    val name = ctx.symbol(0).original
    val calledProcedure = procedure.parent.getProcedures().find { it.name == name }
      ?: throw ctx.illegal("no such procedure '$name'")
    if (calledProcedure.getParams().size != ctx.symbol().size - 1 + ctx.term().size)
      throw ctx.illegal("mismatched arguments for procedure '$name'")

    val (inputParams, outputParams) = calledProcedure.getParams().partition { (_, dir) -> dir == ParamDirection.IN }
    val inputs = inputParams.map { it.first }.zip(ctx.term()).associate { (param, term) ->
      param to termTransformer.toExpr(term.original, param.type)
    }
    val outputs = outputParams.map { it.first }.zip(ctx.symbol().drop(1)).associate { (param, arg) ->
      param to symbolTable.getVar(arg.original).ref
    }
    val args = calledProcedure.getParams().map { (param, _) ->
      inputs[param] ?: outputs[param] ?: throw ctx.illegal("mismatched arguments for procedure '$name'")
    }

    current = current.extend(InvokeLabel(name, args, metadata = ctx.metadata))
  }

  override fun visitReturnStatement(ctx: ReturnStatementContext) {
    procedure.addEdge(
      XcfaEdge(current, procedure.finalLoc.get(), NopLabel, ctx.metadata)
    )

    current = newLoc()
  }

  override fun visitLabelStatement(ctx: LabelStatementContext) {
    labeledLocations[ctx.symbol().original] = current
  }

  override fun visitGotoStatement(ctx: GotoStatementContext) {
    val to = newLoc()
    val placeholder = XcfaEdge(current, to, NopLabel, ctx.metadata)
    procedure.addEdge(placeholder)
    gotos[placeholder] = ctx.symbol().original
    current = to
  }

  override fun visitChoiceStatement(ctx: ChoiceStatementContext) {
    val choiceStart = current
    val choiceEnd = newLoc()

    ctx.statement().forEach { stmtContext ->
      current = choiceStart
      visit(stmtContext)
      procedure.addEdge(
        XcfaEdge(current, choiceEnd, NopLabel, SvLibSourceMetadata("choice"))
      )
    }

    current = choiceEnd
  }

  override fun visitAnnotatedStatement(ctx: AnnotatedStatementContext) {
    val tags = ctx.attributeSvLib().filterIsInstance<TagAttributeContext>().map { it.symbol().original }.toSet()
    current = current.extend(NopLabel, tags)
    tags.forEach { taggedLocations.getOrPut(it, { mutableSetOf() }).add(current) }

    val annotatedStart = current
    visit(ctx.statement())
    val annotatedEnd = current

    ctx.attributeSvLib().filterIsInstance<TagPropertyContext>().forEach { attribute ->
      when (val property = attribute.property()) {
        is CheckTruePropertyContext -> {
          current = procedure.insertCheck(annotatedStart, termTransformer.toExpr(property.relationalTerm().original, Bool()))
        }
        else -> property.unsupported("property '${property.original}'")
      }
    }

    current = annotatedEnd
  }

  private fun applyGotos() {
    gotos.forEach { (placeholder, label) ->
      val labeledLocation = labeledLocations[label]
        ?: throw IllegalStateException("Invalid goto statement: no such label '$label' in procedure '${procedure.name}'")
      val goto = XcfaEdge(
        placeholder.source,
        labeledLocation,
        NopLabel,
        metadata = placeholder.metadata
      )
      procedure.removeEdge(placeholder)
      procedure.addEdge(goto)
    }
  }

  private fun XcfaLocation.extend(label: XcfaLabel, locationTags: Set<String> = setOf()): XcfaLocation {
    val to = newLoc(locationTags)
    procedure.addEdge(XcfaEdge(this, to, label, label.metadata))
    return to
  }

  private val ParserRuleContext.metadata: SvLibSourceMetadata
    get() = SvLibSourceMetadata(original)
}

private data class Loop(val head: XcfaLocation, val exit: XcfaLocation)
