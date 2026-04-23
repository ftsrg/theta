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
package hu.bme.mit.theta.frontend.transformation.model.statements;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.bvtype.BvExprs;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.frontend.ParseContext;
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArithmeticType;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.CInteger;

public final class CMixedSemantics {

    private CMixedSemantics() {}

    public static boolean isMixedArithmetic(final ParseContext parseContext) {
        return parseContext.getArithmetic() == ArithmeticType.mixed;
    }

    public static Expr<BvType> castToBitwiseOperand(
            final Expr<?> expr, final CComplexType type, final ParseContext parseContext) {
        final Expr<?> castExpr = type.castTo(expr);
        if (castExpr.getType() instanceof BvType bvType) {
            return cast(castExpr, bvType);
        }
        checkState(isMixedArithmetic(parseContext), "Bitwise operators require bitvector mode");
        checkState(castExpr.getType() instanceof IntType, "Mixed bitwise operands must be Int");
        final Expr<BvType> converted =
                BvExprs.ToBv(cast(castExpr, IntType.getInstance()), getBitvectorType(type));
        parseContext.getMetadata().create(converted, "cType", type);
        return converted;
    }

    public static Expr<?> castFromBitwiseResult(
            final Expr<BvType> expr, final CComplexType type, final ParseContext parseContext) {
        Expr<?> result = expr;
        if (isMixedArithmetic(parseContext)) {
            result = BvExprs.ToInt(expr);
            parseContext.getMetadata().create(result, "cType", type);
        }
        result = type.castTo(result);
        parseContext.getMetadata().create(result, "cType", type);
        return result;
    }

    public static BvType getBitvectorType(final CComplexType type) {
        checkState(type instanceof CInteger, "Bitwise operators require integer operands");
        return BvType.of(type.width(), ((CInteger) type).isSsigned());
    }
}
