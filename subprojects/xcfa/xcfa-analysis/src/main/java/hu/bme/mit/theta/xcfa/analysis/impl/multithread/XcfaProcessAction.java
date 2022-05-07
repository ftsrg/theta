/*
 *  Copyright 2022 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.xcfa.analysis.impl.multithread;

import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;

import java.util.ArrayList;
import java.util.List;

public class XcfaProcessAction extends StmtAction {
    private final XcfaEdge edge;
    private final List<Stmt> stmts;

    public XcfaProcessAction(final XcfaEdge edge) {
        this.edge = edge;
        stmts = new ArrayList<>();
        for (XcfaLabel label : edge.getLabels()) {
            stmts.add(label.getStmt());
        }
    }

    @Override
    public List<Stmt> getStmts() {
        return stmts;
    }

    public XcfaEdge getEdge() {
        return edge;
    }
}
