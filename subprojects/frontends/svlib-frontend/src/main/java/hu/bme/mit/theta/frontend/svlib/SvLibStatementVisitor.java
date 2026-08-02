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
import static hu.bme.mit.theta.core.stmt.Stmts.Havoc;
import static hu.bme.mit.theta.frontend.svlib.SvLibUtils.boolExpr;
import static hu.bme.mit.theta.frontend.svlib.SvLibUtils.expr;
import static hu.bme.mit.theta.frontend.svlib.SvLibUtils.relationalBoolExpr;
import static hu.bme.mit.theta.frontend.svlib.SvLibUtils.resolveVar;
import static hu.bme.mit.theta.frontend.svlib.SvLibUtils.unsupported;
import static hu.bme.mit.theta.xcfa.utils.UtilsKt.AssignStmtLabel;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
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
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.BiFunction;

final class SvLibStatementVisitor extends SvLibBaseVisitor<XcfaLocation> {

    private final XcfaProcedureBuilder builder;
    private final Map<String, VarDecl<?>> declarations;
    private final BiFunction<String, Boolean, XcfaLocation> nextLoc;
    private final Set<XcfaLocation> terminalLocations = new HashSet<>();
    private XcfaLocation currentEntry;

    SvLibStatementVisitor(
            XcfaProcedureBuilder builder,
            Map<String, VarDecl<?>> declarations,
            BiFunction<String, Boolean, XcfaLocation> nextLoc) {
        this.builder = builder;
        this.declarations = declarations;
        this.nextLoc = nextLoc;
    }

    XcfaLocation visit(SvLibParser.StatementContext statement, XcfaLocation entry) {
        currentEntry = entry;
        XcfaLocation result = super.visit(statement);
        return result == null ? entry : result;
    }

    boolean isTerminal(XcfaLocation location) {
        return terminalLocations.contains(location);
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
            if (terminalLocations.contains(last)) {
                break;
            }
        }
        return last;
    }

    @Override
    public XcfaLocation visitAnnotatedStatement(SvLibParser.AnnotatedStatementContext ctx) {
        XcfaLocation statementEntry = addTagLocation(ctx, currentEntry);

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

    private XcfaLocation addTagLocation(
        SvLibParser.AnnotatedStatementContext ctx, XcfaLocation entry) {
        for (SvLibParser.AttributeSvLibContext attribute : ctx.attributeSvLib()) {
            if (attribute instanceof SvLibParser.TagAttributeContext tagAttribute) {
                XcfaLocation taggedEntry = nextLoc.apply(tagAttribute.symbol().getText(), true);
                builder.addEdge(
                    new XcfaEdge(
                        entry,
                        taggedEntry,
                        NopLabel.INSTANCE,
                        taggedEntry.getMetadata()));
                return taggedEntry;
            }
        }
        return entry;
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

        XcfaLocation endLoc = nextLoc.apply("if-end", false);

        boolean thenTerminal = terminalLocations.contains(thenEnd);
        boolean elseTerminal = terminalLocations.contains(elseEnd);

        if (!thenTerminal) {
            builder.addEdge(
                new XcfaEdge(thenEnd, endLoc, NopLabel.INSTANCE, EmptyMetaData.INSTANCE));
        }
        if (!elseTerminal) {
            builder.addEdge(
                new XcfaEdge(elseEnd, endLoc, NopLabel.INSTANCE, EmptyMetaData.INSTANCE));
        }
        if (thenTerminal && elseTerminal) {
            terminalLocations.add(endLoc);
        }

        return endLoc;
    }

    @Override
    public XcfaLocation visitWhileStatement(SvLibParser.WhileStatementContext ctx) {
        XcfaLocation head = currentEntry;

        Expr<BoolType> condition = boolExpr(ctx.term(), builder, declarations);
        XcfaLocation bodyEntry = addLabel(head, new StmtLabel(AssumeStmt.of(condition)));
        XcfaLocation exit = visit(ctx.statement(), bodyEntry);

        if (!terminalLocations.contains(exit)) {
            builder.addEdge(new XcfaEdge(exit, head, NopLabel.INSTANCE, EmptyMetaData.INSTANCE));
        }

        return addLabel(head, new StmtLabel(AssumeStmt.of(BoolExprs.Not(condition))));
    }

    @Override
    public XcfaLocation visitHavocStatement(SvLibParser.HavocStatementContext ctx) {
        List<XcfaLabel> labels = new ArrayList<>();
        for (int i = 0; i < ctx.symbol().size(); i++) {
            VarDecl<?> variable = resolveVar(ctx.symbol(i).getText(), builder, declarations);
            labels.add(new StmtLabel(Havoc(variable)));
        }
        return addLabels(currentEntry, labels, "havoc");
    }

    @Override
    public XcfaLocation visitReturnStatement(SvLibParser.ReturnStatementContext ctx) {
        builder.addEdge(
            new XcfaEdge(
                currentEntry,
                builder.getFinalLoc().orElseThrow(),
                NopLabel.INSTANCE,
                EmptyMetaData.INSTANCE));
        terminalLocations.add(currentEntry);
        return currentEntry;
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
        XcfaLocation to = nextLoc.apply(sourceName, false);
        XcfaLabel label = labels.size() == 1 ? labels.get(0) : new SequenceLabel(labels);
        builder.addEdge(new XcfaEdge(from, to, label, EmptyMetaData.INSTANCE));
        return to;
    }







}
