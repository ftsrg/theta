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

package hu.bme.mit.theta.analysis.algorithm.ic3;

import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And;

import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.FalseExpr;
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.solver.UCSolver;
import hu.bme.mit.theta.solver.utils.WithPushPop;
import java.util.HashSet;
import java.util.Set;

public class Node {

    private boolean covered;

    private final boolean coverOpt;

    private final UCSolver solver;

    public Set<Expr<BoolType>> getExprs() {
        return exprs;
    }

    public Node getParent() {
        return parent;
    }

    public void setExprs(Expr<BoolType> expr) {
        if (!covered) {
            exprs = new HashSet<Expr<BoolType>>();
            exprs.add(expr);
        }
    }

    public void addExpr(Expr<BoolType> expr) {
        exprs.add(expr);
    }

    private Set<Expr<BoolType>> exprs;

    private Node parent;

    // checks if its expression covers, the input expression
    private boolean isCoveredBy(Expr<BoolType> expr) {
        if (!coverOpt || parent == null) {
            return false;
        }
        final boolean thisCovers;
        try (var wpp = new WithPushPop(solver)) {
            solver.track(PathUtils.unfold(SmartBoolExprs.Not(And(parent.getExprs())), 0));
            solver.track(PathUtils.unfold(expr, 0));
            thisCovers = solver.check().isUnsat();
        }
        if (thisCovers) {
            return true;
        } else if (parent == null) {
            return false;
        } else {
            return parent.isCoveredBy(expr);
        }
    }

    public Node(Expr<BoolType> expr, Node parent, boolean coverOpt, UCSolver solver) {
        exprs = Containers.createSet();
        this.solver = solver;
        this.coverOpt = coverOpt;
        if (parent != null) {
            covered = parent.isCoveredBy(expr);
        } else {
            covered = false;
        }

        if (covered) {
            exprs.add(FalseExpr.getInstance());
        } else {
            exprs.add(expr);
        }
        this.parent = parent;
    }
}
