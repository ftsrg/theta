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

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.collect.ImmutableList.toImmutableList;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.MultiaryExpr;
import java.util.List;

public abstract class AddExpr<ExprType extends Additive<ExprType>>
        extends MultiaryExpr<ExprType, ExprType> {

    protected AddExpr(final Iterable<? extends Expr<ExprType>> ops) {
        super(ops);
    }

    public static <ExprType extends Additive<ExprType>> AddExpr<?> create2(
            final List<? extends Expr<?>> ops) {
        checkArgument(!ops.isEmpty());
        @SuppressWarnings("unchecked")
        final ExprType type = (ExprType) ops.get(0).getType();
        return type.Add(ops.stream().map(op -> cast(op, type)).collect(toImmutableList()));
    }
}
