/*
 *  Copyright 2017 Budapest University of Technology and Economics
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
import hu.bme.mit.theta.core.stmt.xcfa.*;
import hu.bme.mit.theta.core.type.Type;

import java.util.Collection;

/** Collects all variables that are written to by a stmt.
 * Used for collecting data dependencies between stmts. */
final class WrittenVarCollectorStmtVisitor extends XcfaStmtVisitorBase<Collection<VarDecl<?>>, Void> {

    private static final class LazyHolder {
        private final static WrittenVarCollectorStmtVisitor INSTANCE = new WrittenVarCollectorStmtVisitor();
    }

    private WrittenVarCollectorStmtVisitor() {
    }

    static WrittenVarCollectorStmtVisitor getInstance() {
        return WrittenVarCollectorStmtVisitor.LazyHolder.INSTANCE;
    }

    @Override
    public Void visit(XcfaCallStmt stmt, Collection<VarDecl<?>> param) {
        // TODO the procedure's local variables are not added.
        // This is not a problem for xcfa-analysis, as they are not global vars.
        return null;
    }

    @Override
    public Void visit(StoreStmt storeStmt, Collection<VarDecl<?>> param) {
        param.add(storeStmt.getRhs());
        return null;
    }

    @Override
    public Void visit(LoadStmt loadStmt, Collection<VarDecl<?>> param) {
        param.add(loadStmt.getLhs());
        return null;
    }

    @Override
    public Void visit(AtomicBeginStmt atomicBeginStmt, Collection<VarDecl<?>> param) {
        // TODO collect all variables that are accessed from here?
        return null;
    }

    @Override
    public Void visit(AtomicEndStmt atomicEndStmt, Collection<VarDecl<?>> param) {
        return null;
    }

    @Override
    public Void visit(NotifyAllStmt notifyAllStmt, Collection<VarDecl<?>> param) {
        param.add(notifyAllStmt.getSyncVar());
        return null;
    }

    @Override
    public Void visit(NotifyStmt notifyStmt, Collection<VarDecl<?>> param) {
        param.add(notifyStmt.getSyncVar());
        return null;
    }

    @Override
    public Void visit(WaitStmt waitStmt, Collection<VarDecl<?>> param) {
        param.add(waitStmt.getSyncVar());
        return null;
    }

    @Override
    public Void visit(SkipStmt stmt, Collection<VarDecl<?>> param) {
        return null;
    }

    @Override
    public Void visit(AssumeStmt stmt, Collection<VarDecl<?>> param) {
        return null;
    }

    @Override
    public <DeclType extends Type> Void visit(AssignStmt<DeclType> stmt, Collection<VarDecl<?>> param) {
        param.add(stmt.getVarDecl());
        return null;
    }

    @Override
    public <DeclType extends Type> Void visit(HavocStmt<DeclType> stmt, Collection<VarDecl<?>> param) {
        param.add(stmt.getVarDecl());
        return null;
    }

    @Override
    public Void visit(XcfaStmt xcfaStmt, Collection<VarDecl<?>> param) {
        xcfaStmt.accept(this, param);
        return null;
    }

    @Override
    public Void visit(LockStmt lockStmt, Collection<VarDecl<?>> param) {
        param.add(lockStmt.getSyncVar());
        return null;
    }

    @Override
    public Void visit(UnlockStmt unlockStmt, Collection<VarDecl<?>> param) {
        // TODO is this needed here?
        param.add(unlockStmt.getSyncVar());
        return null;
    }

    @Override
    public Void visit(ExitWaitStmt exitWaitStmt, Collection<VarDecl<?>> param) {
        param.add(exitWaitStmt.getSyncVar());
        return null;
    }

    @Override
    public Void visit(EnterWaitStmt enterWaitStmt, Collection<VarDecl<?>> param) {
        param.add(enterWaitStmt.getSyncVar());
        return null;
    }
}
