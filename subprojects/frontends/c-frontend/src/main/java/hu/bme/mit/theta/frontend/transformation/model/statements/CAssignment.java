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

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs;
import hu.bme.mit.theta.core.type.bvtype.BvExprs;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.frontend.ParseContext;
import hu.bme.mit.theta.frontend.UnsupportedFrontendElementException;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import java.util.List;

public class CAssignment extends CStatement {

    private final Expr<?> lValue;
    private final CStatement rValue;
    private final String operator;

    public CAssignment(
            Expr<?> lValue, CStatement rValue, String operator, ParseContext parseContext) {
        super(parseContext);
        checkNotNull(rValue.getExpression());
        this.lValue = lValue;
        this.rValue = rValue;
        rValue.setParent(this);
        this.operator = operator;
    }

    public CStatement getrValue() {
        return rValue;
    }

    public Expr<?> getlValue() {
        return lValue;
    }

    public String getOperator() {
        return operator;
    }

    @Override
    public Expr<?> getExpression() {
        return lValue;
    }

    @Override
    public <P, R> R accept(CStatementVisitor<P, R> visitor, P param) {
        return visitor.visit(this, param);
    }

    @SuppressWarnings("unchecked")
    public Expr<?> getrExpression() {
        Expr<?> ret = null;
        final var rExpression = rValue.getExpression();
        final var type = CComplexType.getType(lValue, parseContext);
        final var castLValue = type.castTo(lValue);
        final var castRValue = type.castTo(rExpression);
        switch (operator) {
            case "=":
                return rExpression;
            case "*=":
                ret = AbstractExprs.Mul(castLValue, castRValue);
                break;
            case "/=":
                if (castLValue.getType() instanceof IntType
                        && castRValue.getType() instanceof IntType) {
                    ret = CIntegerSemantics.createIntDiv(castLValue, castRValue);
                } else {
                    ret = AbstractExprs.Div(castLValue, castRValue);
                }
                break;
            case "%=":
                if (castLValue.getType() instanceof IntType
                        && castRValue.getType() instanceof IntType) {
                    ret = CIntegerSemantics.createIntMod(castLValue, castRValue);
                } else if (castLValue.getType() instanceof BvType
                        && castRValue.getType() instanceof BvType) {
                    ret = AbstractExprs.Rem(castLValue, castRValue);
                } else {
                    ret = AbstractExprs.Mod(castLValue, castRValue);
                }
                break;
            case "+=":
                ret = AbstractExprs.Add(castLValue, castRValue);
                break;
            case "-=":
                ret = AbstractExprs.Sub(castLValue, castRValue);
                break;
            case "<<=":
            case ">>=":
                final var shiftType =
                        CComplexType.getSmallestCommonType(
                                List.of(CComplexType.getType(castLValue, parseContext)),
                                parseContext);
                Expr<BvType> shiftLeftExpr =
                        CMixedSemantics.castToBitwiseOperand(
                                castLValue, shiftType, parseContext);
                Expr<BvType> shiftRightExpr =
                        CMixedSemantics.castToBitwiseOperand(
                                castRValue, shiftType, parseContext);
                Expr<BvType> shiftResult;
                if (operator.equals(">>=")) {
                    if (CMixedSemantics.getBitvectorType(shiftType).getSigned()) {
                        shiftResult = BvExprs.ArithShiftRight(shiftLeftExpr, shiftRightExpr);
                    } else {
                        shiftResult = BvExprs.LogicShiftRight(shiftLeftExpr, shiftRightExpr);
                    }
                } else {
                    shiftResult = BvExprs.ShiftLeft(shiftLeftExpr, shiftRightExpr);
                }
                parseContext.getMetadata().create(shiftResult, "cType", shiftType);
                ret = CMixedSemantics.castFromBitwiseResult(shiftResult, shiftType, parseContext);
                break;
            case "^=":
                ret =
                        CMixedSemantics.castFromBitwiseResult(
                                BvExprs.Xor(
                                        List.of(
                                                CMixedSemantics.castToBitwiseOperand(
                                                        castLValue, type, parseContext),
                                                CMixedSemantics.castToBitwiseOperand(
                                                        castRValue, type, parseContext))),
                                type,
                                parseContext);
                break;
            case "&=":
                ret =
                        CMixedSemantics.castFromBitwiseResult(
                                BvExprs.And(
                                        List.of(
                                                CMixedSemantics.castToBitwiseOperand(
                                                        castLValue, type, parseContext),
                                                CMixedSemantics.castToBitwiseOperand(
                                                        castRValue, type, parseContext))),
                                type,
                                parseContext);
                break;
            case "|=":
                ret =
                        CMixedSemantics.castFromBitwiseResult(
                                BvExprs.Or(
                                        List.of(
                                                CMixedSemantics.castToBitwiseOperand(
                                                        castLValue, type, parseContext),
                                                CMixedSemantics.castToBitwiseOperand(
                                                        castRValue, type, parseContext))),
                                type,
                                parseContext);
                break;
            default:
                throw new UnsupportedFrontendElementException("Unsupported operator: " + operator);
        }
        parseContext.getMetadata().create(ret, "cType", CComplexType.getType(lValue, parseContext));
        ret = CComplexType.getType(lValue, parseContext).castTo(ret);
        parseContext.getMetadata().create(ret, "cType", CComplexType.getType(lValue, parseContext));
        return ret;
    }
}
