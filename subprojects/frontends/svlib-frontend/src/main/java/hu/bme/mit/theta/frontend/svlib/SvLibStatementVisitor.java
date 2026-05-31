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


import static hu.bme.mit.theta.frontend.svlib.SvLibUtils.boolExpr;
import static hu.bme.mit.theta.frontend.svlib.SvLibUtils.expr;
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

final class SvLibStatementVisitor extends SvLibBaseVisitor<Set<XcfaLocation>> {

    private final XcfaProcedureBuilder builder;
    private final Map<String, VarDecl<?>> declarations;
    private final Function<String, XcfaLocation> nextLoc;
    private Set<XcfaLocation> currentEntries = Set.of();

    SvLibStatementVisitor(
            XcfaProcedureBuilder builder,
            Map<String, VarDecl<?>> declarations,
            Function<String, XcfaLocation> nextLoc) {
        this.builder = builder;
        this.declarations = declarations;
        this.nextLoc = nextLoc;
    }

    Set<XcfaLocation> visit(SvLibParser.StatementContext statement, Set<XcfaLocation> entries) {
        currentEntries = entries;
        Set<XcfaLocation> result = super.visit(statement);
        return result == null ? Set.of() : result;
    }

    @Override
    public Set<XcfaLocation> visitAssumeStatement(SvLibParser.AssumeStatementContext ctx) {
        Set<XcfaLocation> result = new LinkedHashSet<>();
        Expr<BoolType> condition = boolExpr(ctx.term(), builder, declarations);
        for (XcfaLocation entry : currentEntries) {
            result.add(addLabel(entry, new StmtLabel(AssumeStmt.of(condition))));
        }
        return result;
    }

    @Override
    public Set<XcfaLocation> visitAssignStatement(SvLibParser.AssignStatementContext ctx) {
        List<XcfaLabel> labels = new ArrayList<>();
        for (int i = 0; i < ctx.symbol().size(); i++) {
            VarDecl<?> variable = resolveVar(ctx.symbol(i).getText(), builder, declarations);
            labels.add(
                AssignStmtLabel(
                    variable,
                    expr(ctx.term(i), variable.getType(), builder, declarations),
                    EmptyMetaData.INSTANCE));
        }

        Set<XcfaLocation> result = new LinkedHashSet<>();
        for (XcfaLocation entry : currentEntries) {
            result.add(addLabels(entry, labels, "assign"));
        }
        return result;
    }

    @Override
    public Set<XcfaLocation> visitSequenceStatement(SvLibParser.SequenceStatementContext ctx) {
        Set<XcfaLocation> entries = currentEntries;
        for (SvLibParser.StatementContext statement : ctx.statement()) {
            entries = visit(statement, entries);
        }
        return entries;
    }

    @Override
    public Set<XcfaLocation> visitAnnotatedStatement(SvLibParser.AnnotatedStatementContext ctx) {
        return visit(ctx.statement(), currentEntries);
    }

    @Override
    public Set<XcfaLocation> visitIfStatement(SvLibParser.IfStatementContext ctx) {
        Expr<BoolType> condition = boolExpr(ctx.term(), builder, declarations);
        Set<XcfaLocation> thenEntries = new LinkedHashSet<>();
        Set<XcfaLocation> elseEntries = new LinkedHashSet<>();
        for (XcfaLocation entry : currentEntries) {
            thenEntries.add(addLabel(entry, new StmtLabel(AssumeStmt.of(condition))));
            elseEntries.add(
                addLabel(entry, new StmtLabel(AssumeStmt.of(BoolExprs.Not(condition)))));
        }
        Set<XcfaLocation> thenExits = visit(ctx.statement(0), thenEntries);
        Set<XcfaLocation> elseExits =
            ctx.statement().size() > 1 ? visit(ctx.statement(1), elseEntries) : elseEntries;
        Set<XcfaLocation> result = new LinkedHashSet<>(thenExits);
        result.addAll(elseExits);
        return result;
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
