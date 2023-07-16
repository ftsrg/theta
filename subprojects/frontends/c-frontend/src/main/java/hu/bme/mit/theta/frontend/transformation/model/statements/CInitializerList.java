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

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.arraytype.ArrayInitExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.frontend.ParseContext;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Add;

//TODO: designators
public class CInitializerList extends CStatement {
    private final List<Tuple2<Optional<CStatement>, CStatement>> statements;
    private final CComplexType type;

    public CInitializerList(CComplexType type, ParseContext parseContext) {
        super(parseContext);
        this.type = type;
        this.statements = new ArrayList<>();
    }

    @Override
    public Expr<?> getExpression() {
        return getTemplatedExpression();
    }

    @Override
    public <P, R> R accept(CStatementVisitor<P, R> visitor, P param) {
        return visitor.visit(this, param);
    }

    @SuppressWarnings("unchecked")
    private <I extends Type, E extends Type> Expr<?> getTemplatedExpression() {
        List<Tuple2<Expr<I>, Expr<E>>> list = new ArrayList<>();
        LitExpr<I> currentValue = (LitExpr<I>) CComplexType.getUnsignedLong(parseContext).getNullValue();
        LitExpr<I> unitValue = (LitExpr<I>) CComplexType.getUnsignedLong(parseContext).getUnitValue();
        for (Tuple2<Optional<CStatement>, CStatement> cStatement : statements) {
            Expr<E> expr = (Expr<E>) type.castTo(cStatement.get2().getExpression());
            list.add(Tuple2.of(currentValue, expr));
            currentValue = (LitExpr<I>) Add(currentValue, unitValue).eval(ImmutableValuation.empty());
        }
        ArrayInitExpr<I, E> aie = ArrayInitExpr.of(list,
                (Expr<E>) type.getNullValue(),
                (ArrayType<I, E>) ArrayType.of(CComplexType.getUnsignedLong(parseContext).getSmtType(), type.getSmtType()));
        parseContext.getMetadata().create(aie, "cType", new CArray(type.getOrigin(), type, parseContext));
        return aie;
    }

    public void addStatement(CStatement index, CStatement value) {
        statements.add(Tuple2.of(Optional.ofNullable(index), value));
    }

    public List<Tuple2<Optional<CStatement>, CStatement>> getStatements() {
        return statements;
    }
}
