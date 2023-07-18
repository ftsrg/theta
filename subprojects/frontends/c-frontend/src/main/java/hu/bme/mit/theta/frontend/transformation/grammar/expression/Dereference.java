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

package hu.bme.mit.theta.frontend.transformation.grammar.expression;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.UnaryExpr;

/**
 * TODO: should this really inherit from expr?
 */
public class Dereference<R extends Type, T extends Type> extends UnaryExpr<R, T> {

    private static final int HASH_SEED = 6988;
    private static final String label = "*";
    private final T type;

    private Dereference(Expr<R> op, T type) {
        super(op);
        this.type = type;
    }

    public static <R extends Type, T extends Type> Dereference<R, T> of(Expr<R> op, T type) {
        return new Dereference<>(op, type);
    }

    @Override
    public T getType() {
        return type;
    }

    @Override
    public LitExpr<T> eval(Valuation val) {
        throw new IllegalStateException(
                "Reference/Dereference expressions are not meant to be evaluated!");
    }

    @Override
    public UnaryExpr<R, T> with(Expr<R> op) {
        return of(op, type);
    }

    @Override
    protected int getHashSeed() {
        return HASH_SEED;
    }

    @Override
    public String getOperatorLabel() {
        return label;
    }
}
