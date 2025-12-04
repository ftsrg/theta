/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.frontend.transformation.grammar.preprocess;

import hu.bme.mit.theta.c.frontend.dsl.gen.CParser;
import hu.bme.mit.theta.c.frontend.dsl.gen.CParser.DirectDeclaratorArray1Context;
import hu.bme.mit.theta.c.frontend.dsl.gen.CParser.DirectDeclaratorArray2Context;
import hu.bme.mit.theta.c.frontend.dsl.gen.CParser.DirectDeclaratorArray3Context;
import hu.bme.mit.theta.c.frontend.dsl.gen.CParser.DirectDeclaratorArray4Context;
import hu.bme.mit.theta.c.frontend.dsl.gen.CParser.MultiplicativeExpressionContext;
import hu.bme.mit.theta.frontend.ParseContext;
import hu.bme.mit.theta.frontend.transformation.grammar.IncludeHandlingCBaseVisitor;
import java.util.List;
import java.util.Set;

public class BitwiseChecker extends IncludeHandlingCBaseVisitor<Void> {
    private final ParseContext parseContext;

    private BitwiseChecker(ParseContext parseContext) {
        this.parseContext = parseContext;
    }

    public static Set<ArithmeticTrait> gatherArithmeticTraits(
            ParseContext parseContext, List<CParser.ExternalDeclarationContext> contexts) {
        BitwiseChecker instance = new BitwiseChecker(parseContext);
        for (CParser.ExternalDeclarationContext ctx : contexts) {
            ctx.accept(instance);
        }
        return instance.parseContext.getArithmeticTraits();
    }

    @Override
    public Void visitTypeSpecifierDouble(CParser.TypeSpecifierDoubleContext ctx) {
        parseContext.addArithmeticTrait(ArithmeticTrait.FLOAT);
        return null;
    }

    @Override
    public Void visitTypeSpecifierFloat(CParser.TypeSpecifierFloatContext ctx) {
        parseContext.addArithmeticTrait(ArithmeticTrait.FLOAT);
        return null;
    }

    @Override
    public Void visitDirectDeclaratorArray1(DirectDeclaratorArray1Context ctx) {
        parseContext.addArithmeticTrait(ArithmeticTrait.ARR);
        return null;
    }

    @Override
    public Void visitDirectDeclaratorArray2(DirectDeclaratorArray2Context ctx) {
        parseContext.addArithmeticTrait(ArithmeticTrait.ARR);
        return null;
    }

    @Override
    public Void visitDirectDeclaratorArray3(DirectDeclaratorArray3Context ctx) {
        parseContext.addArithmeticTrait(ArithmeticTrait.ARR);
        return null;
    }

    @Override
    public Void visitDirectDeclaratorArray4(DirectDeclaratorArray4Context ctx) {
        parseContext.addArithmeticTrait(ArithmeticTrait.ARR);
        return null;
    }

    @Override
    public Void visitPrimaryExpressionConstant(CParser.PrimaryExpressionConstantContext ctx) {
        String text = ctx.getText();
        if (text.contains(".")) {
            parseContext.addArithmeticTrait(ArithmeticTrait.FLOAT);
            return null;
        }
        return super.visitPrimaryExpressionConstant(ctx);
    }

    @Override
    public Void visitInclusiveOrExpression(CParser.InclusiveOrExpressionContext ctx) {
        ctx.exclusiveOrExpression(0).accept(this);
        boolean b = ctx.exclusiveOrExpression().size() > 1;
        if (b) {
            parseContext.addArithmeticTrait(ArithmeticTrait.BITWISE);
        }
        return null;
    }

    @Override
    public Void visitExclusiveOrExpression(CParser.ExclusiveOrExpressionContext ctx) {
        ctx.andExpression(0).accept(this);
        boolean b = ctx.andExpression().size() > 1;
        if (b) {
            parseContext.addArithmeticTrait(ArithmeticTrait.BITWISE);
        }
        return null;
    }

    @Override
    public Void visitAndExpression(CParser.AndExpressionContext ctx) {
        ctx.equalityExpression(0).accept(this);
        boolean b = ctx.equalityExpression().size() > 1;
        if (b) {
            parseContext.addArithmeticTrait(ArithmeticTrait.BITWISE);
        }
        return null;
    }

    @Override
    public Void visitShiftExpression(CParser.ShiftExpressionContext ctx) {
        ctx.additiveExpression(0).accept(this);
        boolean b = ctx.additiveExpression().size() > 1;
        if (b) {
            parseContext.addArithmeticTrait(ArithmeticTrait.BITWISE);
        }
        return null;
    }

    @Override
    public Void visitMultiplicativeExpression(MultiplicativeExpressionContext ctx) {
        if (ctx.castExpression().size() > 1) {
            parseContext.addArithmeticTrait(ArithmeticTrait.NONLIN_INT);
        }
        return super.visitMultiplicativeExpression(ctx);
    }

    @Override
    public Void visitUnaryOperator(CParser.UnaryOperatorContext ctx) {
        if (ctx.getText().equals("~")) {
            parseContext.addArithmeticTrait(ArithmeticTrait.BITWISE);
        }
        return super.visitUnaryOperator(ctx);
    }
}
