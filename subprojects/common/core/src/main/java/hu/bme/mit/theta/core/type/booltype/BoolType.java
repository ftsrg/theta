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
package hu.bme.mit.theta.core.type.booltype;

import hu.bme.mit.theta.core.type.DomainSize;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.Equational;
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr;

public final class BoolType implements Equational<BoolType> {

    private static final BoolType INSTANCE = new BoolType();
    private static final int HASH_SEED = 754364;
    private static final String TYPE_LABEL = "Bool";

    private BoolType() {
    }

    public static BoolType getInstance() {
        return INSTANCE;
    }

    @Override
    public int hashCode() {
        return HASH_SEED;
    }

    @Override
    public boolean equals(final Object obj) {
        return obj instanceof BoolType;
    }

    @Override
    public String toString() {
        return TYPE_LABEL;
    }

    ////

    @Override
    public IffExpr Eq(final Expr<BoolType> leftOp, final Expr<BoolType> rightOp) {
        return BoolExprs.Iff(leftOp, rightOp);
    }

    @Override
    public NeqExpr<BoolType> Neq(final Expr<BoolType> leftOp, final Expr<BoolType> rightOp) {
        return BoolExprs.Xor(leftOp, rightOp);
    }

    @Override
    public DomainSize getDomainSize() {
        return DomainSize.TWO;
    }

}
