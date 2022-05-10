/*
 *  Copyright 2022 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.cat.dsl;

import hu.bme.mit.theta.analysis.algorithm.mcm.MCM;
import hu.bme.mit.theta.analysis.algorithm.mcm.MCMConstraint;
import hu.bme.mit.theta.analysis.algorithm.mcm.MCMRelation;
import hu.bme.mit.theta.analysis.algorithm.mcm.rules.*;
import hu.bme.mit.theta.cat.dsl.gen.CatBaseVisitor;
import hu.bme.mit.theta.cat.dsl.gen.CatParser;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.cat.dsl.CatDslManager.setupCatAntlr;
import static java.lang.Character.isUpperCase;

public class CatVisitor extends CatBaseVisitor<MCMRelation> {
    private MCM mcm;
    private int ruleNameCnt = 0;
    private final File file;
    private final Map<String, MCMRelation> relations;
    private final Map<String, CatParser.FunctionDefContext> functions;
    private final Map<String, CatParser.ProcDefContext> procedures;
    private final Map<String, MCMRelation> paramAssignment;
    private static final Set<String> unaryRelations = Set.of("W", "R", "F", "U");

    public CatVisitor(final File file) {
        this.relations = new LinkedHashMap<>();
        this.procedures = new LinkedHashMap<>();
        this.functions = new LinkedHashMap<>();
        this.paramAssignment = new LinkedHashMap<>();
        this.file = file;
    }

    public MCM getMcm() {
        return mcm;
    }

    private MCMRelation getOrCreateRelation(final String name, final int arity) {
        if(paramAssignment.containsKey(name)) {
            final MCMRelation mcmRelation = paramAssignment.get(name);
            return mcmRelation;
        }
        if(relations.containsKey(name)) {
            final MCMRelation mcmRelation = relations.get(name);
            return mcmRelation;
        }
        final MCMRelation relation = new MCMRelation(arity, name);
        relations.put(name, relation);
        return relation;
    }

    @Override
    public MCMRelation visitMcm(CatParser.McmContext ctx) {
        this.mcm = new MCM(ctx.name() == null ? "Unnamed" : ctx.name().getText());

        final File file = new File(this.file.getParent() + File.separator + "stdlib.cat");
        visitIncludedFile(file);

        return super.visitMcm(ctx);
    }

    private void visitIncludedFile(File file) {
        if(file.exists() && file.isFile()) {
            try {
                final CatParser.McmContext context = setupCatAntlr(file);
                context.scopeBody().accept(this);
            } catch (IOException e) {
                e.printStackTrace();
            }
        } else throw new RuntimeException(new FileNotFoundException(file.getAbsolutePath()));
    }

    @Override
    public MCMRelation visitIncludeFile(CatParser.IncludeFileContext ctx) {
        final File file = new File(this.file.getParent() + File.separator + ctx.file.getText());
        visitIncludedFile(file);
        return null;
    }

    @Override
    public MCMRelation visitAcyclicDefinition(CatParser.AcyclicDefinitionContext ctx) {
        final MCMRelation rule = ctx.e.accept(this);
        mcm.addConstraint(new MCMConstraint(rule, ctx.negate == null ? MCMConstraint.ConstraintType.ACYCLIC : MCMConstraint.ConstraintType.CYCLIC));
        return null;
    }

    @Override
    public MCMRelation visitIrreflexiveDefinition(CatParser.IrreflexiveDefinitionContext ctx) {
        final MCMRelation rule = ctx.e.accept(this);
        mcm.addConstraint(new MCMConstraint(rule, ctx.negate == null ? MCMConstraint.ConstraintType.IRREFLEXIVE : MCMConstraint.ConstraintType.REFLEXIVE));
        return null;
    }

    @Override
    public MCMRelation visitEmptyDefinition(CatParser.EmptyDefinitionContext ctx) {
        final MCMRelation rule = ctx.e.accept(this);
        mcm.addConstraint(new MCMConstraint(rule, ctx.negate == null ? MCMConstraint.ConstraintType.EMPTY : MCMConstraint.ConstraintType.NOTEMPTY));
        return null;
    }

    @Override
    public MCMRelation visitFunctionDef(CatParser.FunctionDefContext ctx) {
        functions.put(ctx.n.getText(), ctx);
        return null;
    }

    @Override
    public MCMRelation visitProcDef(CatParser.ProcDefContext ctx) {
        procedures.put(ctx.n.getText(), ctx);
        return null;
    }

    @Override
    public MCMRelation visitExprToid(CatParser.ExprToidContext ctx) {
        MCMRelation rel = ctx.e.accept(this);
        final MCMRelation relation = getOrCreateRelation("rule" + ruleNameCnt++, 2);
        relation.addRule(new Toid(rel));
        return relation;
    }

    @Override
    public MCMRelation visitExprRange(CatParser.ExprRangeContext ctx) {
        MCMRelation rel = ctx.e.accept(this);
        final MCMRelation relation = getOrCreateRelation("rule" + ruleNameCnt++, 1);
        relation.addRule(new Range(rel));
        return relation;
    }

    @Override
    public MCMRelation visitExprDomain(CatParser.ExprDomainContext ctx) {
        MCMRelation rel = ctx.e.accept(this);
        final MCMRelation relation = getOrCreateRelation("rule" + ruleNameCnt++, 1);
        relation.addRule(new Domain(rel));
        return relation;
    }

    @Override
    public MCMRelation visitProcCall(CatParser.ProcCallContext ctx) {
        final CatParser.ProcDefContext procDefContext = procedures.get(ctx.NAME().getText());
        checkNotNull(procDefContext, "Procedure with name " + ctx.NAME().getText() + " does not exist.");
        final List<CatParser.ExpressionContext> e = ctx.params;
        final Map<String, MCMRelation> toReset = new LinkedHashMap<>();
        for (int i = 0; i < e.size(); i++) {
            final String text = procDefContext.params.get(i).getText();
            CatParser.ExpressionContext expressionContext = e.get(i);
            toReset.put(text, paramAssignment.get(text));
            paramAssignment.put(
                    text,
                    expressionContext.accept(this));
        }
        final MCMRelation accept = procDefContext.body.accept(this);
        toReset.forEach((s, mcmRelation) -> {
            if(mcmRelation == null) paramAssignment.remove(s);
            else paramAssignment.put(s, mcmRelation);
        });
        return accept;
    }

    @Override
    public MCMRelation visitExprTryWith(CatParser.ExprTryWithContext ctx) {
        return ctx.e.accept(this);
    }

    @Override
    public MCMRelation visitExprFunctionCall(CatParser.ExprFunctionCallContext ctx) {
        final CatParser.FunctionDefContext functionDefContext = functions.get(ctx.NAME().getText());
        checkNotNull(functionDefContext, "Function with name " + ctx.NAME().getText() + " does not exist.");
        List<CatParser.ExpressionContext> e = ctx.e;
        final Map<String, MCMRelation> toReset = new LinkedHashMap<>();
        for (int i = 0; i < e.size(); i++) {
            final String text = functionDefContext.params.get(i).getText();
            CatParser.ExpressionContext expressionContext = e.get(i);
            toReset.put(text, paramAssignment.get(text));
            paramAssignment.put(
                    text,
                    expressionContext.accept(this));
        }
        final MCMRelation accept = functionDefContext.e.accept(this);
        toReset.forEach((s, mcmRelation) -> {
            if(mcmRelation == null) paramAssignment.remove(s);
            else paramAssignment.put(s, mcmRelation);
        });
        return accept;
    }

    @Override
    public MCMRelation visitLetDefinition(CatParser.LetDefinitionContext ctx) {
        String name = ctx.NAME().getText();
        CatParser.ExpressionContext eCtx = ctx.e;

        relations.remove(name);
        for (CatParser.LetAndDefinitionContext letAndDefinitionContext : ctx.letAndDefinition()) {
            name = letAndDefinitionContext.NAME().getText();
            relations.remove(name);
        }
        MCMRelation rel = eCtx.accept(this);
        final MCMRelation relation = getOrCreateRelation(ctx.NAME().getText(), rel.getArity());
        relation.addRule(new Self(rel));
        for (CatParser.LetAndDefinitionContext letAndDefinitionContext : ctx.letAndDefinition()) {
            name = letAndDefinitionContext.NAME().getText();
            eCtx = letAndDefinitionContext.e;
            rel = eCtx.accept(this);

            final MCMRelation relationAnd = getOrCreateRelation(name, rel.getArity());
            relationAnd.addRule(new Self(rel));
        }

        return relation;
    }

    @Override
    public MCMRelation visitExprCartesian(CatParser.ExprCartesianContext ctx) {
        MCMRelation rel = ctx.e1.accept(this);
        final MCMRelation relation = getOrCreateRelation("rule" + ruleNameCnt++, 2);
        relation.addRule(new CartesianProduct(rel, ctx.e2.accept(this)));
        return relation;
    }

    @Override
    public MCMRelation visitExprBasic(CatParser.ExprBasicContext ctx) {
        return getOrCreateRelation(ctx.NAME().getText(), isUpperCase(ctx.NAME().getText().charAt(0)) ? 1 : 2);
    }

    @Override
    public MCMRelation visitExprMinus(CatParser.ExprMinusContext ctx) {
        MCMRelation rel = ctx.e1.accept(this);
        final MCMRelation relation = getOrCreateRelation("rule" + ruleNameCnt++, rel.getArity());
        relation.addRule(new Difference(rel, ctx.e2.accept(this)));
        return relation;
    }

    @Override
    public MCMRelation visitExprUnion(CatParser.ExprUnionContext ctx) {
        MCMRelation rel = ctx.e1.accept(this);
        final MCMRelation relation = getOrCreateRelation("rule" + ruleNameCnt++, rel.getArity());
        relation.addRule(new Union(rel, ctx.e2.accept(this)));
        return relation;
    }

    @Override
    public MCMRelation visitExprComposition(CatParser.ExprCompositionContext ctx) {
        MCMRelation rel = ctx.e1.accept(this);
        final MCMRelation relation = getOrCreateRelation("rule" + ruleNameCnt++, rel.getArity());
        relation.addRule(new Sequence(rel, ctx.e2.accept(this)));
        return relation;
    }

    @Override
    public MCMRelation visitExprIntersection(CatParser.ExprIntersectionContext ctx) {
        MCMRelation rel = ctx.e1.accept(this);
        final MCMRelation relation = getOrCreateRelation("rule" + ruleNameCnt++, rel.getArity());
        relation.addRule(new Intersection(rel, ctx.e2.accept(this)));
        return relation;
    }

    @Override
    public MCMRelation visitExprTransitive(CatParser.ExprTransitiveContext ctx) {
        MCMRelation rel = ctx.e.accept(this);
        final MCMRelation relation = getOrCreateRelation("rule" + ruleNameCnt++, rel.getArity());
        relation.addRule(new TransitiveClosure(rel));
        return relation;
    }

    @Override
    public MCMRelation visitExprComplement(CatParser.ExprComplementContext ctx) {
        MCMRelation rel = ctx.e.accept(this);
        final MCMRelation relation = getOrCreateRelation("rule" + ruleNameCnt++, rel.getArity());
        relation.addRule(new Complement(rel));
        return relation;
    }

    @Override
    public MCMRelation visitExprInverse(CatParser.ExprInverseContext ctx) {
        MCMRelation rel = ctx.e.accept(this);
        final MCMRelation relation = getOrCreateRelation("rule" + ruleNameCnt++, rel.getArity());
        relation.addRule(new Inverse(rel));
        return relation;
    }

    @Override
    public MCMRelation visitExprTransRef(CatParser.ExprTransRefContext ctx) {
        MCMRelation rel = ctx.e.accept(this);
        final MCMRelation relation = getOrCreateRelation("rule" + ruleNameCnt++, rel.getArity());
        relation.addRule(new ReflexiveTransitiveClosure(rel));
        return relation;
    }

    @Override
    public MCMRelation visitExpr(CatParser.ExprContext ctx) {
        return ctx.e.accept(this);
    }

    @Override
    public MCMRelation visitExprOptional(CatParser.ExprOptionalContext ctx) {
        MCMRelation rel = ctx.e.accept(this);
        final MCMRelation relation = getOrCreateRelation("rule" + ruleNameCnt++, rel.getArity());
        relation.addRule(new IdentityClosure(rel));
        return relation;
    }

    @Override
    public MCMRelation visitExprNull(CatParser.ExprNullContext ctx) {
        final MCMRelation relation = getOrCreateRelation("rule" + ruleNameCnt++, 1);
        relation.addRule(new EmptyRelation());
        return relation;
    }

    @Override
    public String toString() {
        return mcm.toString();
    }
}
