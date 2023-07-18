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

package hu.bme.mit.theta.analysis.algorithm.mcm.cegar;

import hu.bme.mit.theta.common.Tuple3;
import hu.bme.mit.theta.core.stmt.*;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;

public class StmtTreeUnfolder {
    public static Tuple3<Collection<Expr<BoolType>>, VarIndexing, VarIndexing> unfold(final Stmt stmt, final VarIndexing lhs, final VarIndexing rhs) {
        Visitor visitor = new Visitor(lhs, rhs);
        return Tuple3.of(stmt.accept(visitor, rhs), visitor.getLhsIndexing(), visitor.getRhsIndexing());
    }

    private static class Visitor implements StmtVisitor<VarIndexing, Collection<Expr<BoolType>>> {
        private VarIndexing lhsIndexing;
        private VarIndexing rhsIndexing;

        public Visitor(final VarIndexing lhsIndexing, final VarIndexing rhsIndexing) {
            this.lhsIndexing = lhsIndexing;
            this.rhsIndexing = rhsIndexing;
        }

        @Override
        public Collection<Expr<BoolType>> visit(SkipStmt stmt, VarIndexing rhsIndexing) {
            return List.of();
        }

        @Override
        public Collection<Expr<BoolType>> visit(AssumeStmt stmt, VarIndexing rhsIndexing) {
            return List.of(PathUtils.unfold(stmt.getCond(), rhsIndexing));
        }

        @Override
        public <DeclType extends Type> Collection<Expr<BoolType>> visit(AssignStmt<DeclType> stmt, VarIndexing rhsIndexing) {
            lhsIndexing = lhsIndexing.inc(stmt.getVarDecl());
            List<Expr<BoolType>> eq = List.of(Eq(stmt.getVarDecl().getConstDecl(lhsIndexing.get(stmt.getVarDecl())).getRef(), PathUtils.unfold(stmt.getExpr(), rhsIndexing)));
            this.rhsIndexing = rhsIndexing.inc(stmt.getVarDecl(), lhsIndexing.get(stmt.getVarDecl()) - rhsIndexing.get(stmt.getVarDecl()));
            return eq;
        }

        @Override
        public <DeclType extends Type> Collection<Expr<BoolType>> visit(HavocStmt<DeclType> stmt, VarIndexing rhsIndexing) {
            lhsIndexing = lhsIndexing.inc(stmt.getVarDecl());
            this.rhsIndexing = rhsIndexing.inc(stmt.getVarDecl(), lhsIndexing.get(stmt.getVarDecl()) - rhsIndexing.get(stmt.getVarDecl()));
            return List.of();
        }

        @Override
        public Collection<Expr<BoolType>> visit(SequenceStmt stmt, VarIndexing rhsIndexing) {
            Collection<Expr<BoolType>> ret = new ArrayList<>();
            for (Stmt stmtStmt : stmt.getStmts()) {
                ret.addAll(stmtStmt.accept(this, rhsIndexing));
            }
            return ret;
        }

        @Override
        public Collection<Expr<BoolType>> visit(NonDetStmt stmt, VarIndexing rhsIndexing) {
            throw new UnsupportedOperationException("Not yet implemented");
        }

        @Override
        public Collection<Expr<BoolType>> visit(OrtStmt stmt, VarIndexing rhsIndexing) {
            throw new UnsupportedOperationException("Not yet implemented");
        }

        @Override
        public Collection<Expr<BoolType>> visit(LoopStmt stmt, VarIndexing rhsIndexing) {
            throw new UnsupportedOperationException("Not yet implemented");
        }

        @Override
        public Collection<Expr<BoolType>> visit(IfStmt stmt, VarIndexing rhsIndexing) {
            throw new UnsupportedOperationException("Not yet implemented");
        }

        public VarIndexing getRhsIndexing() {
            return rhsIndexing;
        }

        public VarIndexing getLhsIndexing() {
            return lhsIndexing;
        }
    }
}
