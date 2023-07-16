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

package hu.bme.mit.theta.frontend.transformation.model.statements;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.frontend.ParseContext;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;

import java.util.LinkedHashMap;
import java.util.Map;

import static com.google.common.base.Preconditions.checkNotNull;

public class CAssignment extends CStatement {

    private final Expr<?> lValue;
    private final CStatement rValue;
    private final String operator;
    private static final Map<Type, VarDecl<ArrayType<?, ?>>> memoryMaps = new LinkedHashMap<>();

    public CAssignment(Expr<?> lValue, CStatement rValue, String operator, ParseContext parseContext) {
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

    public static Map<Type, VarDecl<ArrayType<?, ?>>> getMemoryMaps() {
        return memoryMaps;
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
        switch (operator) {
            case "=":
                return rValue.getExpression();
            case "*=":
                ret = AbstractExprs.Mul(lValue, rValue.getExpression());
                break;
            case "/=":
                ret = AbstractExprs.Div(lValue, rValue.getExpression());
                break;
            case "%=":
                ret = AbstractExprs.Mod(lValue, rValue.getExpression());
                break;
            case "+=":
                ret = AbstractExprs.Add(lValue, rValue.getExpression());
                break;
            case "-=":
                ret = AbstractExprs.Sub(lValue, rValue.getExpression());
                break;
            default:
                throw new RuntimeException("Bad operator!");
        }
        parseContext.getMetadata().create(ret, "cType", CComplexType.getType(lValue, parseContext));
        ret = CComplexType.getType(lValue, parseContext).castTo(ret);
        parseContext.getMetadata().create(ret, "cType", CComplexType.getType(lValue, parseContext));
        return ret;
    }
}
