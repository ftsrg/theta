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
package hu.bme.mit.theta.analysis.multi.stmt;

import static com.google.common.base.Preconditions.checkArgument;

import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.analysis.multi.MultiAction;
import hu.bme.mit.theta.core.stmt.Stmt;
import java.util.List;

public final class StmtMultiAction<L extends StmtAction, R extends StmtAction> extends StmtAction
        implements MultiAction<L, R> {
    private final L leftAction;
    private final R rightAction;

    private StmtMultiAction(L lAction, R rAction) {
        checkArgument(
                (lAction != null && rAction == null) || (rAction != null && lAction == null),
                "One of the actions should be null while the other not");
        leftAction = lAction;
        rightAction = rAction;
    }

    public static <L extends StmtAction, R extends StmtAction>
            StmtMultiAction<L, R> ofLeftStmtAction(L action) {
        return new StmtMultiAction<>(action, null);
    }

    public static <L extends StmtAction, R extends StmtAction>
            StmtMultiAction<L, R> ofRightStmtAction(R action) {
        return new StmtMultiAction<>(null, action);
    }

    public StmtAction getAction() {
        return getLeftAction() == null ? getRightAction() : getLeftAction();
    }

    @Override
    public String toString() {
        return "ExprMultiAction{"
                + "leftAction="
                + leftAction
                + ", rightAction="
                + rightAction
                + '}';
    }

    @Override
    public List<Stmt> getStmts() {
        return getAction().getStmts();
    }

    @Override
    public L getLeftAction() {
        return leftAction;
    }

    @Override
    public R getRightAction() {
        return rightAction;
    }
}
