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

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.frontend.ParseContext;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

public class CCompound extends CStatement {

    private final List<CStatement> cStatementList;

    public CCompound(ParseContext parseContext) {
        super(parseContext);
        cStatementList = new ArrayList<>();
    }

    /**
     * @return Unmodifiable list of statements
     */
    public List<CStatement> getcStatementList() {
        return Collections.unmodifiableList(cStatementList);
    }

    public void insertCStatementsToFront(List<CStatement> cStatements) {
        cStatementList.addAll(0, cStatements);
        cStatementList.forEach(e -> e.setParent(this));
    }

    public void addCStatement(CStatement cStatement) {
        cStatementList.add(cStatement);
        cStatement.setParent(this);
    }

    @Override
    public Expr<?> getExpression() {
        return cStatementList.get(cStatementList.size() - 1).getExpression();
    }

    @Override
    public void setPostStatements(CStatement postStatements) {
        this.postStatements = postStatements;
        if (postStatements != null) postStatements.setParent(this);
    }

    @Override
    public void setPreStatements(CStatement preStatements) {
        this.preStatements = preStatements;
        if (preStatements != null) preStatements.setParent(this);
    }

    @Override
    public <P, R> R accept(CStatementVisitor<P, R> visitor, P param) {
        return visitor.visit(this, param);
    }
}
