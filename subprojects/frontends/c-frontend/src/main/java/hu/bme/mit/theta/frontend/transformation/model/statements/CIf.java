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

import hu.bme.mit.theta.frontend.ParseContext;

public class CIf extends CStatement {

    private final CStatement guard;
    private final CStatement body;
    private final CStatement elseStatement;

    public CIf(
            CStatement guard,
            CStatement body,
            CStatement elseStatement,
            ParseContext parseContext) {
        super(parseContext);
        this.guard = guard;
        if (guard != null) guard.setParent(this);
        this.body = body;
        if (body != null) body.setParent(this);
        this.elseStatement = elseStatement;
        if (elseStatement != null) elseStatement.setParent(this);
    }

    public CStatement getElseStatement() {
        return elseStatement;
    }

    public CStatement getBody() {
        return body;
    }

    public CStatement getGuard() {
        return guard;
    }

    @Override
    public <P, R> R accept(CStatementVisitor<P, R> visitor, P param) {
        return visitor.visit(this, param);
    }
}
