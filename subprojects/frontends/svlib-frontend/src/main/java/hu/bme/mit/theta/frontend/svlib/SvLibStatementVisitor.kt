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
import hu.bme.mit.theta.svlib.frontend.dsl.gen.SvLibParser.*
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.AssignStmtLabel
import org.antlr.v4.runtime.CharStream

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
  private val loops = ArrayDeque<Loop>()

  override fun visitAssumeStatement(ctx: AssumeStatementContext) {
    val condition = termTransformer.toExpr(ctx.term().original, Bool())
    current = current.extend(StmtLabel(Stmts.Assume(condition), metadata = SvLibSourceMetadata(ctx.original)))
  }

  override fun visitAssignStatement(ctx: AssignStatementContext) {
    val labels = ctx.symbol().zip(ctx.term()).map { (symbol, term) ->
      val variable = symbolTable.getVar(symbol.original)
      AssignStmtLabel(
        variable,
        termTransformer.toExpr(term.original, variable.getType()),
        SvLibSourceMetadata("(assign ${symbol.original} ${term.original})")
      )
    }

    current = current.extend(SequenceLabel(labels, metadata = SvLibSourceMetadata(ctx.original)))
  }

  override fun visitHavocStatement(ctx: HavocStatementContext) {
    val labels = ctx.symbol().map { symbol ->
      val variable = symbolTable.getVar(symbol.original)
      StmtLabel(Stmts.Havoc(variable), metadata = SvLibSourceMetadata("(havoc ${symbol.original})"))
    }
    val label = if (labels.size == 1) labels.first() else SequenceLabel(labels, metadata = SvLibSourceMetadata(ctx.original))

    current = current.extend(label)
  }

  override fun visitSequenceStatement(ctx: SequenceStatementContext) = ctx.statement().forEach(::visit)

  override fun visitIfStatement(ctx: IfStatementContext) {
    val condition = termTransformer.toExpr(ctx.term().original, Bool())
    val ifStart = current
    val ifEnd = newLoc()

    current = ifStart.extend(StmtLabel(Stmts.Assume(condition), metadata = SvLibSourceMetadata(ctx.term().original)))
    visit(ctx.statement(0))
    procedure.addEdge(XcfaEdge(current, ifEnd, NopLabel, EmptyMetaData))

    current = ifStart.extend(StmtLabel(Stmts.Assume(Not(condition)), metadata = SvLibSourceMetadata(ctx.term().original)))
    if (ctx.statement().size > 1) visit(ctx.statement(1))
    procedure.addEdge(XcfaEdge(current, ifEnd, NopLabel, EmptyMetaData))

    current = ifEnd
  }

  override fun visitWhileStatement(ctx: WhileStatementContext) {
    val condition = termTransformer.toExpr(ctx.term().original, Bool())
    val loopHead = current
    val loopExit = loopHead.extend(StmtLabel(Stmts.Assume(Not(condition)), metadata = SvLibSourceMetadata(ctx.term().original)))

    loops.push(Loop(loopHead, loopExit))
    current = loopHead.extend(StmtLabel(Stmts.Assume(condition), metadata = SvLibSourceMetadata(ctx.term().original)))
    visit(ctx.statement())
    procedure.addEdge(XcfaEdge(current, loopHead, NopLabel, EmptyMetaData))
    loops.pop()

    current = loopExit
  }

  override fun visitContinueStatement(ctx: ContinueStatementContext) {
    if (loops.isEmpty()) throw ctx.unsupported("continue outside while")

    procedure.addEdge(
      XcfaEdge(current, loops.peak().head, NopLabel, SvLibSourceMetadata(ctx.original))
    )

    current = newLoc()
  }

  override fun visitBreakStatement(ctx: BreakStatementContext) {
    if (loops.isEmpty()) throw ctx.unsupported("break outside while")

    procedure.addEdge(
      XcfaEdge(current, loops.peak().exit, NopLabel, SvLibSourceMetadata(ctx.original))
    )

    current = newLoc()
  }

  override fun visitCallStatement(ctx: CallStatementContext) = throw ctx.unsupported("call")

  override fun visitReturnStatement(ctx: ReturnStatementContext) {
    procedure.addEdge(
      XcfaEdge(current, procedure.finalLoc.get(), NopLabel, SvLibSourceMetadata(ctx.original))
    )

    current = newLoc()
  }

  override fun visitLabelStatement(ctx: LabelStatementContext) = throw ctx.unsupported("label")

  override fun visitGotoStatement(ctx: GotoStatementContext) = throw ctx.unsupported("goto")

  override fun visitChoiceStatement(ctx: ChoiceStatementContext) = throw ctx.unsupported("choice")

  override fun visitAnnotatedStatement(ctx: AnnotatedStatementContext) {
    val tags = ctx.attributeSvLib().filterIsInstance<TagAttributeContext>().map { it.symbol().original }
    current = current.extend(NopLabel, tags)
    tags.forEach { taggedLocations.getOrPut(it, { mutableSetOf() }).add(current) }

    ctx.attributeSvLib().filterIsInstance<TagPropertyContext>().forEach { attribute ->
      when (val property = attribute.property()) {
        is CheckTruePropertyContext -> {
          current = procedure.insertCheck(current, termTransformer.toExpr(property.relationalTerm().original, Bool()))
        }
        else -> warn("Unsupported SV-LIB property: '${property.original}'")
      }
    }

    visit(ctx.statement())
  }

  private fun XcfaLocation.extend(label: XcfaLabel, locationTags: List<String> = listOf()): XcfaLocation {
    val to = newLoc(locationTags)
    procedure.addEdge(XcfaEdge(this, to, label, label.metadata))
    return to
  }
}

private data class Loop(val head: XcfaLocation, val exit: XcfaLocation)
