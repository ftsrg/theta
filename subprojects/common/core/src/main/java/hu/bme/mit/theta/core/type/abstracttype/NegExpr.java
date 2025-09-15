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
package hu.bme.mit.theta.core.type.abstracttype;

import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.UnaryExpr;

public abstract class NegExpr<ExprType extends Additive<ExprType>>
        extends UnaryExpr<ExprType, ExprType> {

    protected NegExpr(final Expr<ExprType> op) {
        super(op);
    }

    public static <ExprType extends Additive<ExprType>> NegExpr<?> create2(final Expr<?> op) {
        @SuppressWarnings("unchecked")
        final ExprType type = (ExprType) op.getType();
        final Expr<ExprType> newOp = cast(op, type);
        return type.Neg(newOp);
    }
}
