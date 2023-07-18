/*
 *  Copyright 2023 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.c.frontend.dsl.gen.CBaseVisitor;
import hu.bme.mit.theta.c.frontend.dsl.gen.CParser;
import hu.bme.mit.theta.frontend.ParseContext;

import java.util.List;

import static com.google.common.base.Preconditions.checkState;

public class BitwiseChecker extends CBaseVisitor<Void> {
    private BitwiseOption bitwiseOption = null;

    // checks only once, returns the result of the first check after
    public static BitwiseOption checkIfBitwise(ParseContext parseContext, List<CParser.ExternalDeclarationContext> contexts) {
        BitwiseChecker instance = new BitwiseChecker();
        instance.bitwiseOption = BitwiseOption.INTEGER;
        for (CParser.ExternalDeclarationContext ctx : contexts) {
            ctx.accept(instance);
        }
        checkState(instance.bitwiseOption != null);
        parseContext.setBitwiseOption(instance.bitwiseOption);
        return instance.bitwiseOption;
    }

    @Override
    public Void visitTypeSpecifierDouble(CParser.TypeSpecifierDoubleContext ctx) {
        bitwiseOption = BitwiseOption.BITWISE_FLOAT;
        return null;
    }

    @Override
    public Void visitTypeSpecifierFloat(CParser.TypeSpecifierFloatContext ctx) {
        bitwiseOption = BitwiseOption.BITWISE_FLOAT;
        return null;
    }

    @Override
    public Void visitPrimaryExpressionConstant(CParser.PrimaryExpressionConstantContext ctx) {
        String text = ctx.getText();
        if (text.contains(".")) {
            bitwiseOption = BitwiseOption.BITWISE_FLOAT;
            return null;
        }
        return super.visitPrimaryExpressionConstant(ctx);
    }

    @Override
    public Void visitInclusiveOrExpression(CParser.InclusiveOrExpressionContext ctx) {
        ctx.exclusiveOrExpression(0).accept(this);
        Boolean b = ctx.exclusiveOrExpression().size() > 1;
        if (b) {
            if (bitwiseOption == BitwiseOption.INTEGER) {
                bitwiseOption = BitwiseOption.BITWISE;
            }
        }
        return null;
    }

    @Override
    public Void visitExclusiveOrExpression(CParser.ExclusiveOrExpressionContext ctx) {
        ctx.andExpression(0).accept(this);
        Boolean b = ctx.andExpression().size() > 1;
        if (b) {
            if (bitwiseOption == BitwiseOption.INTEGER) {
                bitwiseOption = BitwiseOption.BITWISE;
            }
        }
        return null;
    }

    @Override
    public Void visitAndExpression(CParser.AndExpressionContext ctx) {
        ctx.equalityExpression(0).accept(this);
        Boolean b = ctx.equalityExpression().size() > 1;
        if (b) {
            if (bitwiseOption == BitwiseOption.INTEGER) {
                bitwiseOption = BitwiseOption.BITWISE;
            }
        }
        return null;
    }

    @Override
    public Void visitShiftExpression(CParser.ShiftExpressionContext ctx) {
        ctx.additiveExpression(0).accept(this);
        Boolean b = ctx.additiveExpression().size() > 1;
        if (b) {
            if (bitwiseOption == BitwiseOption.INTEGER) {
                bitwiseOption = BitwiseOption.BITWISE;
            }
        }
        return null;
    }

}
