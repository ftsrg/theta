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

import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.frontend.ParseContext;

import static com.google.common.base.Preconditions.checkNotNull;

public class CAssume extends CStatement {

    private final AssumeStmt assumeStmt;

    public CAssume(AssumeStmt assumeStmt, ParseContext parseContext) {
        super(parseContext);
        checkNotNull(assumeStmt);
        this.assumeStmt = assumeStmt;
    }

    @Override
    public Expr<?> getExpression() {
        return assumeStmt.getCond();
    }

    @Override
    public <P, R> R accept(CStatementVisitor<P, R> visitor, P param) {
        return visitor.visit(this, param);
    }

    public AssumeStmt getAssumeStmt() {
        return assumeStmt;
    }
}
