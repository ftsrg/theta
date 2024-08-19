/*
 *  Copyright 2024 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.core.type.enumtype;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.BinaryExpr;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.abstracttype.EqExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;

public class EnumEqExpr extends EqExpr<EnumType> {

    private static final int HASH_SEED = 5326;
    private static final String OPERATOR_LABEL = "=";

    private EnumEqExpr(Expr<EnumType> leftOp, Expr<EnumType> rightOp) {
        super(leftOp, rightOp);
    }

    public static EnumEqExpr of(Expr<EnumType> leftOp, Expr<EnumType> rightOp) {
        return new EnumEqExpr(leftOp, rightOp);
    }

    @Override
    public BinaryExpr<EnumType, BoolType> with(Expr<EnumType> leftOp, Expr<EnumType> rightOp) {
        if (leftOp == getLeftOp() && rightOp == getRightOp()) {
            return this;
        } else {
            return EnumEqExpr.of(leftOp, rightOp);
        }
    }

    @Override
    public BinaryExpr<EnumType, BoolType> withLeftOp(Expr<EnumType> leftOp) {
        return with(leftOp, getRightOp());
    }

    @Override
    public BinaryExpr<EnumType, BoolType> withRightOp(Expr<EnumType> rightOp) {
        return with(getLeftOp(), rightOp);
    }

    @Override
    protected int getHashSeed() {
        return HASH_SEED;
    }

    @Override
    public String getOperatorLabel() {
        return OPERATOR_LABEL;
    }

    @Override
    public BoolType getType() {
        return Bool();
    }

    @Override
    public LitExpr<BoolType> eval(Valuation val) {
        return EnumLitExpr.eq((EnumLitExpr) getLeftOp().eval(val), (EnumLitExpr) getRightOp().eval(val));
    }
}
