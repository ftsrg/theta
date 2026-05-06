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
package hu.bme.mit.theta.analysis.algorithm.ic3;

import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.*;
import static hu.bme.mit.theta.core.utils.ExprUtils.getConjuncts;

import hu.bme.mit.theta.analysis.algorithm.bounded.MonolithicExpr;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import hu.bme.mit.theta.solver.UCSolver;
import hu.bme.mit.theta.solver.utils.WithPushPop;
import java.util.*;

public class Frame {
    private final Frame parent;
    private final List<Clause> clauses;

    private final UCSolver solver;
    private final BaseOptimizations optimizations;
    private final MonolithicExpr monolithicExpr;

    Frame(final Frame parent, UCSolver solver, MonolithicExpr monolithicExpr, BaseOptimizations optimizations) {
        this.parent = parent;
        this.solver = solver;
        this.monolithicExpr = monolithicExpr;
        this.optimizations = optimizations;
        clauses = new ArrayList<>();
    }

    public List<Clause> getClauses() {
        return clauses;
    }

    public Expr<BoolType> getExpression() {
        final List<Expr<BoolType>> exprs = new ArrayList<>();
        for (Clause clause : clauses) {
            exprs.add(clause.toExpr());
        }
        return And(exprs);
    }

    public void addFrameToSolver(VarIndexing indexing) {
        if(parent == null){
            solver.track(PathUtils.unfold(monolithicExpr.getInitExpr(),indexing));
            return;
        }
        for (Clause clause : clauses) {
            solver.track(PathUtils.unfold(clause.toExpr(), indexing));
        }
        if(optimizations.isPropertyOpt()){
            solver.track(PathUtils.unfold(monolithicExpr.getPropExpr(),indexing));
        }
    }
    public void addNegatedFrameToSolver(VarIndexing indexing) {
        if(parent == null){
            solver.track(PathUtils.unfold(Not(monolithicExpr.getInitExpr()),indexing));
            return;
        }
        final List<Expr<BoolType>> exprs = new ArrayList<>();
        for (Clause clause : clauses) {
            exprs.add(clause.negate().toExpr());
        }
        if(optimizations.isPropertyOpt()) {
            exprs.add(Not(monolithicExpr.getPropExpr()));
        }
        solver.track(PathUtils.unfold(Or(exprs),indexing));
    }
    public void refine(Cube blockedCube) {
        Clause newClause = blockedCube.negate();
        Clause oldClause = null;
        for (Clause clause : clauses) {

            if(clause.subsumes(newClause)){
                oldClause = clause;
            }
            if(newClause.subsumes(clause)){
                return;
            }
        }

        if(oldClause != null){
            clauses.remove(oldClause);
        }
        clauses.add(newClause);
    }

    public Valuation checkIfTargetIsReachableValuation(Expr<BoolType> target) {
        try (var wpp = new WithPushPop(solver)) {
            addFrameToSolver(VarIndexingFactory.indexing(0));
            getConjuncts(monolithicExpr.getTransExpr())
                .forEach(ex -> solver.track(PathUtils.unfold(ex, 0)));
            solver.track(PathUtils.unfold(target, monolithicExpr.getTransOffsetIndex()));
            if (solver.check().isSat()) {
                return solver.getModel();
            } else {
                return null;
            }
        }
    }

    public Valuation checkIfContainsValuation(Expr<BoolType> target) {
        try (var wpp = new WithPushPop(solver)) {
            solver.track(PathUtils.unfold(target, 0));
            addFrameToSolver(VarIndexingFactory.indexing(0));
            if (solver.check().isSat()) {
                return solver.getModel();
            } else {
                return null;
            }
        }
    }

    public boolean equalsAllParents() {
        if (this.parent == null) {
            return false;
        }
        try (var wpp = new WithPushPop(solver)) {
            var currentParent = this.parent;
            while(currentParent!=null){
                currentParent.addNegatedFrameToSolver(VarIndexingFactory.indexing(0));
                currentParent = currentParent.parent;
            }

            addFrameToSolver(VarIndexingFactory.indexing(0));

            return solver.check().isUnsat();
        }
    }

    public boolean equalsParent() {
        if (this.parent == null) {
            return false;
        }
        try (var wpp = new WithPushPop(solver)) {

            parent.addNegatedFrameToSolver(VarIndexingFactory.indexing(0));
            addFrameToSolver(VarIndexingFactory.indexing(0));

            return solver.check().isUnsat();
        }
    }
}
