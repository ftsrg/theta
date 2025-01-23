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

    public Expr<?> getrExpression() {
        Expr<?> ret = null;
        final var rExpression = rValue.getExpression();
        final var type = CComplexType.getType(lValue, parseContext);
        switch (operator) {
            case "=":
                return rExpression;
            case "*=":
                ret = AbstractExprs.Mul(type.castTo(lValue), type.castTo(rExpression));
                break;
            case "/=":
                ret = AbstractExprs.Div(type.castTo(lValue), type.castTo(rExpression));
                break;
            case "%=":
                ret = AbstractExprs.Mod(type.castTo(lValue), type.castTo(rExpression));
                break;
            case "+=":
                ret = AbstractExprs.Add(type.castTo(lValue), type.castTo(rExpression));
                break;
            case "-=":
                ret = AbstractExprs.Sub(type.castTo(lValue), type.castTo(rExpression));
                break;
            case "^=":
                checkState(
                        lValue.getType() instanceof BvType
                                && rExpression.getType() instanceof BvType);
                ret =
                        BvExprs.Xor(
                                List.of(
                                        (Expr<BvType>) type.castTo(lValue),
                                        (Expr<BvType>) type.castTo(rExpression)));
                break;
            case "&=":
                checkState(
                        lValue.getType() instanceof BvType
                                && rExpression.getType() instanceof BvType);
                ret =
                        BvExprs.And(
                                List.of(
                                        (Expr<BvType>) type.castTo(lValue),
                                        (Expr<BvType>) type.castTo(rExpression)));
                break;
            case "|=":
                checkState(
                        lValue.getType() instanceof BvType
                                && rExpression.getType() instanceof BvType);
                ret =
                        BvExprs.Or(
                                List.of(
                                        (Expr<BvType>) type.castTo(lValue),
                                        (Expr<BvType>) type.castTo(rExpression)));
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
