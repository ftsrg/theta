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
package hu.bme.mit.theta.frontend.svlib;


import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not;
import static hu.bme.mit.theta.frontend.svlib.SvLibUtils.boolExpr;
import static hu.bme.mit.theta.frontend.svlib.SvLibUtils.expr;
import static hu.bme.mit.theta.frontend.svlib.SvLibUtils.relationalBoolExpr;
import static hu.bme.mit.theta.frontend.svlib.SvLibUtils.resolveVar;
import static hu.bme.mit.theta.frontend.svlib.SvLibUtils.unsupported;
import static hu.bme.mit.theta.xcfa.utils.UtilsKt.AssignStmtLabel;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.svlib.frontend.dsl.gen.SvLibBaseVisitor;
import hu.bme.mit.theta.svlib.frontend.dsl.gen.SvLibParser;
import hu.bme.mit.theta.xcfa.model.EmptyMetaData;
import hu.bme.mit.theta.xcfa.model.NopLabel;
import hu.bme.mit.theta.xcfa.model.SequenceLabel;
import hu.bme.mit.theta.xcfa.model.StmtLabel;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

final class SvLibStatementVisitor extends SvLibBaseVisitor<XcfaLocation> {

    private final XcfaProcedureBuilder builder;
    private final Map<String, VarDecl<?>> declarations;
    private final Function<String, XcfaLocation> nextLoc;
    private XcfaLocation currentEntry;

    SvLibStatementVisitor(
            XcfaProcedureBuilder builder,
            Map<String, VarDecl<?>> declarations,
            Function<String, XcfaLocation> nextLoc) {
        this.builder = builder;
        this.declarations = declarations;
        this.nextLoc = nextLoc;
    }

    XcfaLocation visit(SvLibParser.StatementContext statement, XcfaLocation entry) {
        currentEntry = entry;
        XcfaLocation result = super.visit(statement);
        return result == null ? entry : result;
    }

    @Override
    public XcfaLocation visitAssumeStatement(SvLibParser.AssumeStatementContext ctx) {
        Expr<BoolType> condition = boolExpr(ctx.term(), builder, declarations);
        return addLabel(currentEntry, new StmtLabel(AssumeStmt.of(condition)));
    }

    @Override
    public XcfaLocation visitAssignStatement(SvLibParser.AssignStatementContext ctx) {
        List<XcfaLabel> labels = new ArrayList<>();
        for (int i = 0; i < ctx.symbol().size(); i++) {
            VarDecl<?> variable = resolveVar(ctx.symbol(i).getText(), builder, declarations);
            labels.add(
                AssignStmtLabel(
                    variable,
                    expr(ctx.term(i), variable.getType(), builder, declarations),
                    EmptyMetaData.INSTANCE));
        }
        return addLabels(currentEntry, labels, "assign");
    }

    @Override
    public XcfaLocation visitSequenceStatement(SvLibParser.SequenceStatementContext ctx) {
        XcfaLocation last = currentEntry;
        for (SvLibParser.StatementContext statement : ctx.statement()) {
            last = visit(statement, last);
        }
        return last;
    }

    @Override
    public XcfaLocation visitAnnotatedStatement(SvLibParser.AnnotatedStatementContext ctx) {
        XcfaLocation statementEntry = currentEntry;

        for (SvLibParser.AttributeSvLibContext attribute : ctx.attributeSvLib()) {
            if (attribute instanceof SvLibParser.TagPropertyContext tagProperty
                && tagProperty.property()
                    instanceof SvLibParser.CheckTruePropertyContext checkTrueProperty) {
                Expr<BoolType> condition =
                    relationalBoolExpr(
                        checkTrueProperty.relationalTerm(), builder, declarations);

                builder.addEdge(
                    new XcfaEdge(
                        statementEntry,
                        builder.getErrorLoc().orElseThrow(),
                        new StmtLabel(AssumeStmt.of(Not(condition))),
                        EmptyMetaData.INSTANCE));

                statementEntry =
                    addLabel(statementEntry, new StmtLabel(AssumeStmt.of(condition)));
            }
        }

        return visit(ctx.statement(), statementEntry);
    }

    @Override
    public XcfaLocation visitIfStatement(SvLibParser.IfStatementContext ctx) {
        Expr<BoolType> condition = boolExpr(ctx.term(), builder, declarations);

        XcfaLocation thenEntry =
            addLabel(currentEntry, new StmtLabel(AssumeStmt.of(condition)));

        XcfaLocation elseEntry =
            addLabel(currentEntry, new StmtLabel(AssumeStmt.of(Not(condition))));

        XcfaLocation thenEnd = visit(ctx.statement(0), thenEntry);

        XcfaLocation elseEnd =
            ctx.statement().size() > 1
                ? visit(ctx.statement(1), elseEntry)
                : elseEntry;

        XcfaLocation endLoc = nextLoc.apply("if-end");

        builder.addEdge(new XcfaEdge(thenEnd, endLoc, NopLabel.INSTANCE, EmptyMetaData.INSTANCE));
        builder.addEdge(new XcfaEdge(elseEnd, endLoc, NopLabel.INSTANCE, EmptyMetaData.INSTANCE));

        return endLoc;
    }

    @Override
    public XcfaLocation visitWhileStatement(SvLibParser.WhileStatementContext ctx) {
        XcfaLocation head = currentEntry;

        Expr<BoolType> condition = boolExpr(ctx.term(), builder, declarations);
        XcfaLocation bodyEntry = addLabel(head, new StmtLabel(AssumeStmt.of(condition)));
        XcfaLocation exit = visit(ctx.statement(), bodyEntry);

        builder.addEdge(new XcfaEdge(exit, head, NopLabel.INSTANCE, EmptyMetaData.INSTANCE));

        return addLabel(head, new StmtLabel(AssumeStmt.of(BoolExprs.Not(condition))));
    }

    private XcfaLocation addLabel(XcfaLocation from, XcfaLabel label) {
        return addLabels(from, List.of(label));
    }

    private XcfaLocation addLabels(XcfaLocation from, List<XcfaLabel> labels) {
        return addLabels(from, labels, "sequence");
    }

    private XcfaLocation addLabels(
        XcfaLocation from, List<XcfaLabel> labels, String sourceName) {
        if (labels.isEmpty()) {
            return from;
        }
        XcfaLocation to = nextLoc.apply(sourceName);
        XcfaLabel label = labels.size() == 1 ? labels.get(0) : new SequenceLabel(labels);
        builder.addEdge(new XcfaEdge(from, to, label, EmptyMetaData.INSTANCE));
        return to;
    }







}
