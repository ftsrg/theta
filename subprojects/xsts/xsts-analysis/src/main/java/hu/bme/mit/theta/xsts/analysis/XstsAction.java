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
package hu.bme.mit.theta.xsts.analysis;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.stmt.Stmt;

import java.util.List;

public final class XstsAction extends StmtAction {

    private final List<Stmt> stmts;

    private XstsAction(final List<Stmt> stmts) {
        this.stmts = stmts;
    }

    public static XstsAction create(final Stmt stmt) {
        return new XstsAction(ImmutableList.of(stmt));
    }

    public static XstsAction create(final List<Stmt> stmts) {
        return new XstsAction(stmts);
    }

    @Override
    public List<Stmt> getStmts() {
        return stmts;
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj != null && this.getClass() == obj.getClass()) {
            final XstsAction that = (XstsAction) obj;
            return this.stmts.equals(that.stmts);
        } else {
            return false;
        }
    }

    @Override
    public String toString() {
        return Utils.lispStringBuilder(getClass().getSimpleName()).body().addAll(stmts).toString();
    }
}
