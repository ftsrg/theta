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
package hu.bme.mit.theta.core.utils;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.*;
import hu.bme.mit.theta.core.type.Type;
import java.util.Collection;

final class WrittenVarCollectorStmtVisitor implements StmtVisitor<Collection<VarDecl<?>>, Void> {

    private static final class LazyHolder {

        private static final WrittenVarCollectorStmtVisitor INSTANCE =
                new WrittenVarCollectorStmtVisitor();
    }

    private WrittenVarCollectorStmtVisitor() {}

    static WrittenVarCollectorStmtVisitor getInstance() {
        return LazyHolder.INSTANCE;
    }

    @Override
    public Void visit(final SkipStmt stmt, final Collection<VarDecl<?>> vars) {
        return null;
    }

    @Override
    public Void visit(final AssumeStmt stmt, final Collection<VarDecl<?>> vars) {
        return null;
    }

    @Override
    public <DeclType extends Type> Void visit(
            final AssignStmt<DeclType> stmt, final Collection<VarDecl<?>> vars) {
        vars.add(stmt.getVarDecl());
        return null;
    }

    @Override
    public <PtrType extends Type, OffsetType extends Type, DeclType extends Type> Void visit(
            MemoryAssignStmt<PtrType, OffsetType, DeclType> stmt, Collection<VarDecl<?>> vars) {
        ExprUtils.collectVars(stmt.getDeref(), vars);
        ExprUtils.collectVars(stmt.getExpr(), vars);
        return null;
    }

    @Override
    public <DeclType extends Type> Void visit(
            final HavocStmt<DeclType> stmt, final Collection<VarDecl<?>> vars) {
        vars.add(stmt.getVarDecl());
        return null;
    }

    @Override
    public Void visit(SequenceStmt stmt, Collection<VarDecl<?>> vars) {
        for (Stmt subStmt : stmt.getStmts()) {
            subStmt.accept(WrittenVarCollectorStmtVisitor.getInstance(), vars);
        }
        return null;
    }

    @Override
    public Void visit(NonDetStmt stmt, Collection<VarDecl<?>> vars) {
        for (Stmt subStmt : stmt.getStmts()) {
            subStmt.accept(WrittenVarCollectorStmtVisitor.getInstance(), vars);
        }
        return null;
    }

    @Override
    public Void visit(OrtStmt stmt, Collection<VarDecl<?>> vars) {
        for (Stmt subStmt : stmt.getStmts()) {
            subStmt.accept(WrittenVarCollectorStmtVisitor.getInstance(), vars);
        }
        return null;
    }

    @Override
    public Void visit(LoopStmt stmt, Collection<VarDecl<?>> vars) {
        ExprUtils.collectVars(stmt.getFrom(), vars);
        ExprUtils.collectVars(stmt.getTo(), vars);
        vars.add(stmt.getLoopVariable());
        return stmt.getStmt().accept(WrittenVarCollectorStmtVisitor.getInstance(), vars);
    }

    public Void visit(IfStmt stmt, Collection<VarDecl<?>> vars) {
        stmt.getThen().accept(WrittenVarCollectorStmtVisitor.getInstance(), vars);
        stmt.getElze().accept(WrittenVarCollectorStmtVisitor.getInstance(), vars);
        return null;
    }
}
