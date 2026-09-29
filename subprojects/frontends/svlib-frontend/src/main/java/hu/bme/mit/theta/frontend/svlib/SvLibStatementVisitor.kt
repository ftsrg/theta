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

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.Stmts
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs
import hu.bme.mit.theta.frontend.svlib.SvLibUtils.nextLoc
import hu.bme.mit.theta.frontend.svlib.SvLibUtils.unsupported
import hu.bme.mit.theta.svlib.frontend.dsl.gen.SvLibBaseVisitor
import hu.bme.mit.theta.svlib.frontend.dsl.gen.SvLibParser.*
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.AssignStmtLabel

internal class SvLibStatementVisitor(
  private val builder: XcfaProcedureBuilder,
  private val declarations: Map<String, VarDecl<*>>,
) : SvLibBaseVisitor<XcfaLocation>() {

  private val terminalLocations: MutableSet<XcfaLocation> = HashSet()
  private val loopExitLocations: ArrayDeque<XcfaLocation> = ArrayDeque()
  private var currentEntry: XcfaLocation? = null

  fun visit(statement: StatementContext, entry: XcfaLocation): XcfaLocation {
    currentEntry = entry
    return super.visit(statement)
  }

  fun isTerminal(location: XcfaLocation): Boolean {
    return terminalLocations.contains(location)
  }

  override fun visitAssumeStatement(ctx: AssumeStatementContext): XcfaLocation {
    val condition = SvLibUtils.boolExpr(ctx.term(), builder, declarations)
    return addLabel(currentEntry!!, StmtLabel(AssumeStmt.of(condition)))
  }

  override fun visitAssignStatement(ctx: AssignStatementContext): XcfaLocation {
    val labels = ctx.symbol().zip(ctx.term()).map { (symbol, term) ->
      val variable = SvLibUtils.resolveVar(symbol.text, builder, declarations)
      AssignStmtLabel(
        variable,
        SvLibUtils.expr(term, variable.getType(), builder, declarations),
        EmptyMetaData
      )
    }

    return addLabels(currentEntry!!, labels, "assign")
  }

  override fun visitSequenceStatement(ctx: SequenceStatementContext): XcfaLocation {
    var last = currentEntry!!

    for (statement in ctx.statement()) {
      last = visit(statement, last)
      if (terminalLocations.contains(last)) {
        break
      }
    }

    return last
  }

  override fun visitAnnotatedStatement(ctx: AnnotatedStatementContext): XcfaLocation {
    var statementEntry = addTagLocation(ctx, currentEntry!!)

    for (attribute in ctx.attributeSvLib()) {
      if (attribute is TagPropertyContext && attribute.property() is CheckTruePropertyContext) {
        val condition = SvLibUtils.relationalBoolExpr(
          (attribute.property() as CheckTruePropertyContext).relationalTerm(), builder, declarations
        )

        builder.addEdge(
          XcfaEdge(
            statementEntry,
            builder.errorLoc.orElseThrow(),
            StmtLabel(AssumeStmt.of(SmartBoolExprs.Not(condition))),
            EmptyMetaData
          )
        )

        statementEntry = addLabel(statementEntry, StmtLabel(AssumeStmt.of(condition)))
      }
    }

    return visit(ctx.statement(), statementEntry)
  }

  private fun addTagLocation(
    ctx: AnnotatedStatementContext, entry: XcfaLocation
  ): XcfaLocation {
    for (attribute in ctx.attributeSvLib()) {
      if (attribute is TagAttributeContext) {
        val taggedEntry = nextLoc(attribute.symbol().getText(), true)
        builder.addEdge(
          XcfaEdge(
            entry,
            taggedEntry,
            NopLabel,
            taggedEntry.metadata
          )
        )
        return taggedEntry
      }
    }
    return entry
  }

  override fun visitIfStatement(ctx: IfStatementContext): XcfaLocation {
    val condition = SvLibUtils.boolExpr(ctx.term(), builder, declarations)

    val thenEntry = addLabel(currentEntry!!, StmtLabel(AssumeStmt.of(condition)))
    val elseEntry = addLabel(currentEntry!!, StmtLabel(AssumeStmt.of(SmartBoolExprs.Not(condition))))
    val thenEnd = visit(ctx.statement(0), thenEntry)
    val elseEnd = if (ctx.statement().size > 1) visit(ctx.statement(1), elseEntry) else elseEntry

    val endLoc = nextLoc("if-end", false)

    val thenTerminal = terminalLocations.contains(thenEnd)
    val elseTerminal = terminalLocations.contains(elseEnd)

    if (!thenTerminal)
      builder.addEdge(XcfaEdge(thenEnd, endLoc, NopLabel, EmptyMetaData))

    if (!elseTerminal)
      builder.addEdge(XcfaEdge(elseEnd, endLoc, NopLabel, EmptyMetaData))

    if (thenTerminal && elseTerminal)
      terminalLocations.add(endLoc)

    return endLoc
  }

  override fun visitWhileStatement(ctx: WhileStatementContext): XcfaLocation {
    val head = currentEntry!!
    val exitLoc = nextLoc("while-exit", false)

    val condition = SvLibUtils.boolExpr(ctx.term(), builder, declarations)
    val bodyEntry = addLabel(head, StmtLabel(AssumeStmt.of(condition)))
    builder.addEdge(
      XcfaEdge(
        head,
        exitLoc,
        StmtLabel(AssumeStmt.of(BoolExprs.Not(condition))),
        EmptyMetaData
      )
    )

    loopExitLocations.addFirst(exitLoc)
    val exit = visit(ctx.statement(), bodyEntry)
    loopExitLocations.removeFirst()

    if (!terminalLocations.contains(exit)) {
      builder.addEdge(XcfaEdge(exit, head, NopLabel, EmptyMetaData))
    }

    return exitLoc
  }

  override fun visitHavocStatement(ctx: HavocStatementContext): XcfaLocation {
    val labels = ctx.symbol().map { symbol ->
      val variable = SvLibUtils.resolveVar(symbol.text, builder, declarations)
      StmtLabel(Stmts.Havoc(variable))
    }

    return addLabels(currentEntry!!, labels, "havoc")
  }

  override fun visitCallStatement(ctx: CallStatementContext) = unsupportedStatement("call")

  override fun visitLabelStatement(ctx: LabelStatementContext) = unsupportedStatement("label")

  override fun visitGotoStatement(ctx: GotoStatementContext) = unsupportedStatement("goto")

  override fun visitBreakStatement(ctx: BreakStatementContext): XcfaLocation {
    if (loopExitLocations.isEmpty()) {
      unsupportedStatement("break outside while")
    }

    builder.addEdge(
      XcfaEdge(
        currentEntry!!,
        loopExitLocations.first(),
        NopLabel,
        EmptyMetaData
      )
    )

    terminalLocations.add(currentEntry!!)

    return currentEntry!!
  }

  override fun visitContinueStatement(ctx: ContinueStatementContext) = unsupportedStatement("continue")


  override fun visitChoiceStatement(ctx: ChoiceStatementContext) = unsupportedStatement("choice")

  override fun visitReturnStatement(ctx: ReturnStatementContext): XcfaLocation {
    builder.addEdge(
      XcfaEdge(
        currentEntry!!,
        builder.finalLoc.orElseThrow(),
        NopLabel,
        EmptyMetaData
      )
    )

    terminalLocations.add(currentEntry!!)

    return currentEntry!!
  }

  private fun unsupportedStatement(statementName: String): Nothing
    = unsupported("statement '$statementName'")

  private fun addLabel(from: XcfaLocation, label: XcfaLabel) = addLabels(from, listOf(label))

  private fun addLabels(
    from: XcfaLocation, labels: List<XcfaLabel>, sourceName: String = "sequence"
  ): XcfaLocation {
    if (labels.isEmpty()) return from

    val to = nextLoc(sourceName, false)
    val label = if (labels.size == 1) labels[0] else SequenceLabel(labels)
    builder.addEdge(XcfaEdge(from, to, label, EmptyMetaData))
    return to
  }
}
