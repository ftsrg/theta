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

import hu.bme.mit.theta.cat.dsl.gen.CatBaseVisitor;
import hu.bme.mit.theta.cat.dsl.gen.CatParser;
import hu.bme.mit.theta.cat.mcm.MCM;
import hu.bme.mit.theta.cat.mcm.MCMConstraint;
import hu.bme.mit.theta.cat.mcm.MCMRelation;
import hu.bme.mit.theta.cat.mcm.rules.CartesianProduct;
import hu.bme.mit.theta.cat.mcm.rules.Complement;
import hu.bme.mit.theta.cat.mcm.rules.Difference;
import hu.bme.mit.theta.cat.mcm.rules.IdentityClosure;
import hu.bme.mit.theta.cat.mcm.rules.Intersection;
import hu.bme.mit.theta.cat.mcm.rules.Inverse;
import hu.bme.mit.theta.cat.mcm.rules.ReflexiveTransitiveClosure;
import hu.bme.mit.theta.cat.mcm.rules.Self;
import hu.bme.mit.theta.cat.mcm.rules.Sequence;
import hu.bme.mit.theta.cat.mcm.rules.TransitiveClosure;
import hu.bme.mit.theta.cat.mcm.rules.Union;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import static com.google.common.base.Preconditions.checkArgument;

public class CatVisitor extends CatBaseVisitor<MCMRelation> {
    private MCM mcm;
    private int ruleNameCnt = 0;
    private final Map<String, MCMRelation> relations;
    private static final Set<String> unaryRelations = Set.of("W", "R", "F", "U");

    public CatVisitor() {
        this.relations = new LinkedHashMap<>();
    }

    public MCM getMcm() {
        return mcm;
    }

    private MCMRelation getOrCreateRelation(final String name) {
        int arity = unaryRelations.contains(name) ? 1 : 2;
        if(relations.containsKey(name)) {
            final MCMRelation mcmRelation = relations.get(name);
            checkArgument(arity == mcmRelation.getArity(), "Arity of relations do not match!");
            return mcmRelation;
        }
        final MCMRelation relation = new MCMRelation(arity, name);
        relations.put(name, relation);
        return relation;
    }

    @Override
    public MCMRelation visitMcm(CatParser.McmContext ctx) {
        this.mcm = new MCM(ctx.NAME() == null ? "Unnamed" : ctx.NAME().getText());
        return super.visitMcm(ctx);
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
    public MCMRelation visitLetDefinition(CatParser.LetDefinitionContext ctx) {
        if(relations.containsKey(ctx.NAME().getText())) throw new RuntimeException("Relation with name " + ctx.NAME().getText() + " already exists.");
        final MCMRelation relation = getOrCreateRelation(ctx.NAME().getText());
        relation.addRule(new Self(ctx.e.accept(this)));
        return relation;
    }

    @Override
    public MCMRelation visitLetRecDefinition(CatParser.LetRecDefinitionContext ctx) {
        if(relations.containsKey(ctx.NAME().getText())) throw new RuntimeException("Relation with name " + ctx.NAME().getText() + " already exists.");
        final MCMRelation relation = getOrCreateRelation(ctx.NAME().getText());
        relation.addRule(new Self(ctx.e.accept(this)));
        return relation;
    }

    @Override
    public MCMRelation visitExprCartesian(CatParser.ExprCartesianContext ctx) {
        final MCMRelation relation = getOrCreateRelation("rule_" + ruleNameCnt++);
        relation.addRule(new CartesianProduct(ctx.e1.accept(this), ctx.e2.accept(this)));
        return relation;
    }

    @Override
    public MCMRelation visitExprRangeIdentity(CatParser.ExprRangeIdentityContext ctx) {
        throw new UnsupportedOperationException("Not yet supported");
    }

    @Override
    public MCMRelation visitExprBasic(CatParser.ExprBasicContext ctx) {
        return getOrCreateRelation(ctx.NAME().getText());
    }

    @Override
    public MCMRelation visitExprMinus(CatParser.ExprMinusContext ctx) {
        final MCMRelation relation = getOrCreateRelation("rule_" + ruleNameCnt++);
        relation.addRule(new Difference(ctx.e1.accept(this), ctx.e2.accept(this)));
        return relation;
    }

    @Override
    public MCMRelation visitExprUnion(CatParser.ExprUnionContext ctx) {
        final MCMRelation relation = getOrCreateRelation("rule_" + ruleNameCnt++);
        relation.addRule(new Union(ctx.e1.accept(this), ctx.e2.accept(this)));
        return relation;
    }

    @Override
    public MCMRelation visitExprComposition(CatParser.ExprCompositionContext ctx) {
        final MCMRelation relation = getOrCreateRelation("rule_" + ruleNameCnt++);
        relation.addRule(new Sequence(ctx.e1.accept(this), ctx.e2.accept(this)));
        return relation;
    }

    @Override
    public MCMRelation visitExprIntersection(CatParser.ExprIntersectionContext ctx) {
        final MCMRelation relation = getOrCreateRelation("rule_" + ruleNameCnt++);
        relation.addRule(new Intersection(ctx.e1.accept(this), ctx.e2.accept(this)));
        return relation;
    }

    @Override
    public MCMRelation visitExprTransitive(CatParser.ExprTransitiveContext ctx) {
        final MCMRelation relation = getOrCreateRelation("rule_" + ruleNameCnt++);
        relation.addRule(new TransitiveClosure(ctx.e.accept(this)));
        return relation;
    }

    @Override
    public MCMRelation visitExprComplement(CatParser.ExprComplementContext ctx) {
        final MCMRelation relation = getOrCreateRelation("rule_" + ruleNameCnt++);
        relation.addRule(new Complement(ctx.e.accept(this)));
        return relation;
    }

    @Override
    public MCMRelation visitExprInverse(CatParser.ExprInverseContext ctx) {
        final MCMRelation relation = getOrCreateRelation("rule_" + ruleNameCnt++);
        relation.addRule(new Inverse(ctx.e.accept(this)));
        return relation;
    }

    @Override
    public MCMRelation visitExprDomainIdentity(CatParser.ExprDomainIdentityContext ctx) {
        throw new UnsupportedOperationException("Not yet supported");
    }

    @Override
    public MCMRelation visitExprIdentity(CatParser.ExprIdentityContext ctx) {
        throw new UnsupportedOperationException("Not yet supported");
    }

    @Override
    public MCMRelation visitExprTransRef(CatParser.ExprTransRefContext ctx) {
        final MCMRelation relation = getOrCreateRelation("rule_" + ruleNameCnt++);
        relation.addRule(new ReflexiveTransitiveClosure(ctx.e.accept(this)));
        return relation;
    }

    @Override
    public MCMRelation visitExprFencerel(CatParser.ExprFencerelContext ctx) {
        throw new UnsupportedOperationException("Not yet supported");
    }

    @Override
    public MCMRelation visitExpr(CatParser.ExprContext ctx) {
        return ctx.e.accept(this);
    }

    @Override
    public MCMRelation visitExprOptional(CatParser.ExprOptionalContext ctx) {
        final MCMRelation relation = getOrCreateRelation("rule_" + ruleNameCnt++);
        relation.addRule(new IdentityClosure(ctx.e.accept(this)));
        return relation;
    }

    @Override
    public String toString() {
        return mcm.toString();
    }
}
