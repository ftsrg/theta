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

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.frontend.ParseContext;
import hu.bme.mit.theta.frontend.UnsupportedFrontendElementException;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

// TODO: designators
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
        throw new UnsupportedFrontendElementException(
                "Cannot create expression of initializer list.");
    }

    @Override
    public <P, R> R accept(CStatementVisitor<P, R> visitor, P param) {
        return visitor.visit(this, param);
    }

    public void addStatement(CStatement index, CStatement value) {
        statements.add(Tuple2.of(Optional.ofNullable(index), value));
    }

    public List<Tuple2<Optional<CStatement>, CStatement>> getStatements() {
        return statements;
    }
}
