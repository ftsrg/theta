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
import hu.bme.mit.theta.common.datalog.Datalog;

public class CatDslVisitor extends CatBaseVisitor<Void> {

    private final Datalog datalogProgram;

    public CatDslVisitor() {
        this.datalogProgram = Datalog.createProgram();
    }

    @Override
    public Void visitAcyclicDefinition(CatParser.AcyclicDefinitionContext ctx) {

        return super.visitAcyclicDefinition(ctx);
    }

    @Override
    public Void visitIrreflexiveDefinition(CatParser.IrreflexiveDefinitionContext ctx) {
        return super.visitIrreflexiveDefinition(ctx);
    }

    @Override
    public Void visitEmptyDefinition(CatParser.EmptyDefinitionContext ctx) {
        return super.visitEmptyDefinition(ctx);
    }

    @Override
    public Void visitLetDefinition(CatParser.LetDefinitionContext ctx) {
        return super.visitLetDefinition(ctx);
    }

    @Override
    public Void visitLetRecDefinition(CatParser.LetRecDefinitionContext ctx) {
        return super.visitLetRecDefinition(ctx);
    }

    @Override
    public Void visitExprCartesian(CatParser.ExprCartesianContext ctx) {
        return super.visitExprCartesian(ctx);
    }

    @Override
    public Void visitExprRangeIdentity(CatParser.ExprRangeIdentityContext ctx) {
        return super.visitExprRangeIdentity(ctx);
    }

    @Override
    public Void visitExprBasic(CatParser.ExprBasicContext ctx) {
        return super.visitExprBasic(ctx);
    }

    @Override
    public Void visitExprMinus(CatParser.ExprMinusContext ctx) {
        return super.visitExprMinus(ctx);
    }

    @Override
    public Void visitExprUnion(CatParser.ExprUnionContext ctx) {
        return super.visitExprUnion(ctx);
    }

    @Override
    public Void visitExprComposition(CatParser.ExprCompositionContext ctx) {
        return super.visitExprComposition(ctx);
    }

    @Override
    public Void visitExprIntersection(CatParser.ExprIntersectionContext ctx) {
        return super.visitExprIntersection(ctx);
    }

    @Override
    public Void visitExprTransitive(CatParser.ExprTransitiveContext ctx) {
        return super.visitExprTransitive(ctx);
    }

    @Override
    public Void visitExprComplement(CatParser.ExprComplementContext ctx) {
        return super.visitExprComplement(ctx);
    }

    @Override
    public Void visitExprInverse(CatParser.ExprInverseContext ctx) {
        return super.visitExprInverse(ctx);
    }

    @Override
    public Void visitExprDomainIdentity(CatParser.ExprDomainIdentityContext ctx) {
        return super.visitExprDomainIdentity(ctx);
    }

    @Override
    public Void visitExprIdentity(CatParser.ExprIdentityContext ctx) {
        return super.visitExprIdentity(ctx);
    }

    @Override
    public Void visitExprTransRef(CatParser.ExprTransRefContext ctx) {
        return super.visitExprTransRef(ctx);
    }

    @Override
    public Void visitExprFencerel(CatParser.ExprFencerelContext ctx) {
        return super.visitExprFencerel(ctx);
    }

    @Override
    public Void visitExpr(CatParser.ExprContext ctx) {
        return super.visitExpr(ctx);
    }

    @Override
    public Void visitExprOptional(CatParser.ExprOptionalContext ctx) {
        return super.visitExprOptional(ctx);
    }
}
