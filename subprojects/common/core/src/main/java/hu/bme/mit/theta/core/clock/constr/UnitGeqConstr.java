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

import static hu.bme.mit.theta.core.type.rattype.RatExprs.Geq;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.rattype.RatGeqExpr;
import hu.bme.mit.theta.core.type.rattype.RatType;

public final class UnitGeqConstr extends UnitConstr {

    private static final int HASH_SEED = 2797;

    private static final String OPERATOR_LABEL = ">=";

    private volatile RatGeqExpr expr = null;

    UnitGeqConstr(final VarDecl<RatType> clock, final int bound) {
        super(clock, bound);
    }

    @Override
    public RatGeqExpr toExpr() {
        RatGeqExpr result = expr;
        if (result == null) {
            final RefExpr<RatType> ref = getVar().getRef();
            result = Geq(ref, Rat(getBound(), 1));
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
            final UnitGeqConstr that = (UnitGeqConstr) obj;
            return this.getBound() == that.getBound() && this.getVar().equals(that.getVar());
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
