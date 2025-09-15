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
package hu.bme.mit.theta.core.clock.constr;

import static hu.bme.mit.theta.core.type.rattype.RatExprs.Leq;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Sub;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.rattype.RatLeqExpr;
import hu.bme.mit.theta.core.type.rattype.RatType;

public final class DiffLeqConstr extends DiffConstr {

    private static final int HASH_SEED = 7019;

    private static final String OPERATOR_LABEL = "<=";

    private volatile RatLeqExpr expr = null;

    DiffLeqConstr(
            final VarDecl<RatType> leftVar, final VarDecl<RatType> rightVar, final int bound) {
        super(leftVar, rightVar, bound);
    }

    @Override
    public RatLeqExpr toExpr() {
        RatLeqExpr result = expr;
        if (result == null) {
            final RefExpr<RatType> leftRef = getLeftVar().getRef();
            final RefExpr<RatType> rightRef = getRightVar().getRef();
            result = Leq(Sub(leftRef, rightRef), Rat(getBound(), 1));
            expr = result;
        }
        return result;
    }

    @Override
    public <P, R> R accept(
            final ClockConstrVisitor<? super P, ? extends R> visitor, final P param) {
        return visitor.visit(this, param);
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj != null && this.getClass() == obj.getClass()) {
            final DiffLeqConstr that = (DiffLeqConstr) obj;
            return this.getBound() == that.getBound()
                    && this.getLeftVar().equals(that.getLeftVar())
                    && this.getRightVar().equals(that.getRightVar());
        } else {
            return false;
        }
    }

    @Override
    protected int getHashSeed() {
        return HASH_SEED;
    }

    @Override
    protected String getOperatorLabel() {
        return OPERATOR_LABEL;
    }
}
