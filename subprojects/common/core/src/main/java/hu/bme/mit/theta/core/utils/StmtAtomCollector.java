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

package hu.bme.mit.theta.core.utils;

import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.stmt.IfStmt;
import hu.bme.mit.theta.core.stmt.LoopStmt;
import hu.bme.mit.theta.core.stmt.NonDetStmt;
import hu.bme.mit.theta.core.stmt.OrtStmt;
import hu.bme.mit.theta.core.stmt.SequenceStmt;
import hu.bme.mit.theta.core.stmt.SkipStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.stmt.StmtVisitor;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.abstracttype.EqExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

import java.util.Set;

public class StmtAtomCollector {

    public static Set<Expr<BoolType>> collectAtoms(final Stmt stmt) {
        final Set<Expr<BoolType>> atoms = Containers.createSet();
        stmt.accept(new AllAssumesAndAssignsCollector(), atoms);
        return atoms;
    }

    private static class AllAssumesAndAssignsCollector implements
            StmtVisitor<Set<Expr<BoolType>>, Void> {

        @Override
        public Void visit(SkipStmt stmt, Set<Expr<BoolType>> atoms) {
            return null;
        }

        @Override
        public Void visit(AssumeStmt stmt, Set<Expr<BoolType>> atoms) {
            atoms.addAll(ExprUtils.getAtoms(stmt.getCond()));
            return null;
        }

        @Override
        public <DeclType extends Type> Void visit(AssignStmt<DeclType> stmt,
                                                  Set<Expr<BoolType>> atoms) {
            final Expr<BoolType> eq = EqExpr.create2(stmt.getVarDecl().getRef(), stmt.getExpr());
            atoms.addAll(ExprUtils.getAtoms(eq));
            return null;
        }

        @Override
        public <DeclType extends Type> Void visit(HavocStmt<DeclType> stmt,
                                                  Set<Expr<BoolType>> atoms) {
            return null;
        }

        @Override
        public Void visit(SequenceStmt stmt, Set<Expr<BoolType>> atoms) {
            stmt.getStmts().forEach(s -> s.accept(this, atoms));
            return null;
        }

        @Override
        public Void visit(NonDetStmt stmt, Set<Expr<BoolType>> atoms) {
            stmt.getStmts().forEach(s -> s.accept(this, atoms));
            return null;
        }

        @Override
        public Void visit(OrtStmt stmt, Set<Expr<BoolType>> atoms) {
            throw new UnsupportedOperationException();
        }

        @Override
        public Void visit(LoopStmt stmt, Set<Expr<BoolType>> atoms) {
            stmt.getStmt().accept(this, atoms);
            return null;
        }

        public Void visit(IfStmt stmt, Set<Expr<BoolType>> atoms) {
            stmt.getThen().accept(this, atoms);
            stmt.getElze().accept(this, atoms);
            atoms.addAll(ExprUtils.getAtoms(stmt.getCond()));
            return null;
        }
    }

}
