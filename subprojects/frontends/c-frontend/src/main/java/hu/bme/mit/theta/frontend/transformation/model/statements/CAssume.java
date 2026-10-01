/*
 *  Copyright 2026 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.frontend.ParseContext;
import java.util.Optional;

public class CAssume extends CStatement {

    private final AssumeStmt assumeStmt;
    private final VarDecl<?> havocked;

    public CAssume(AssumeStmt assumeStmt, ParseContext parseContext) {
        this(null, assumeStmt, parseContext);
    }

    /**
     * An assumption preceded by a havoc of {@code havocked}: a declaration without an initializer,
     * which gives the object a fresh indeterminate value each time it is executed.
     */
    public CAssume(VarDecl<?> havocked, AssumeStmt assumeStmt, ParseContext parseContext) {
        super(parseContext);
        checkNotNull(assumeStmt);
        this.assumeStmt = assumeStmt;
        this.havocked = havocked;
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

    public Optional<VarDecl<?>> getHavocked() {
        return Optional.ofNullable(havocked);
    }
}
