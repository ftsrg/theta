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
package hu.bme.mit.theta.core.type.rattype;

import hu.bme.mit.theta.core.type.DomainSize;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.Additive;
import hu.bme.mit.theta.core.type.abstracttype.Equational;
import hu.bme.mit.theta.core.type.abstracttype.Multiplicative;
import hu.bme.mit.theta.core.type.abstracttype.Ordered;

public final class RatType
        implements Additive<RatType>, Multiplicative<RatType>, Equational<RatType>, Ordered<RatType> {

    private static final RatType INSTANCE = new RatType();
    private static final int HASH_SEED = 385863;
    private static final String TYPE_LABEL = "Rat";

    private RatType() {
    }

    public static RatType getInstance() {
        return INSTANCE;
    }

    @Override
    public int hashCode() {
        return HASH_SEED;
    }

    @Override
    public boolean equals(final Object obj) {
        return (obj instanceof RatType);
    }

    @Override
    public String toString() {
        return TYPE_LABEL;
    }

    ////

    @Override
    public RatAddExpr Add(final Iterable<? extends Expr<RatType>> ops) {
        return RatExprs.Add(ops);
    }

    @Override
    public RatSubExpr Sub(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
        return RatExprs.Sub(leftOp, rightOp);
    }

    @Override
    public RatPosExpr Pos(final Expr<RatType> op) {
        return RatExprs.Pos(op);
    }

    @Override
    public RatNegExpr Neg(final Expr<RatType> op) {
        return RatExprs.Neg(op);
    }

    @Override
    public RatMulExpr Mul(final Iterable<? extends Expr<RatType>> ops) {
        return RatExprs.Mul(ops);
    }

    @Override
    public RatDivExpr Div(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
        return RatExprs.Div(leftOp, rightOp);
    }

    @Override
    public RatEqExpr Eq(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
        return RatExprs.Eq(leftOp, rightOp);
    }

    @Override
    public RatNeqExpr Neq(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
        return RatExprs.Neq(leftOp, rightOp);
    }

    @Override
    public RatLtExpr Lt(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
        return RatExprs.Lt(leftOp, rightOp);
    }

    @Override
    public RatLeqExpr Leq(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
        return RatExprs.Leq(leftOp, rightOp);
    }

    @Override
    public RatGtExpr Gt(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
        return RatExprs.Gt(leftOp, rightOp);
    }

    @Override
    public RatGeqExpr Geq(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
        return RatExprs.Geq(leftOp, rightOp);
    }

    @Override
    public DomainSize getDomainSize() {
        return DomainSize.INFINITY;
    }
}
