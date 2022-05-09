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

import com.google.common.collect.Sets;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.*;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaLabelVisitor;

import java.util.Map;
import java.util.Set;

class XcfaLabelDependencyCollector implements XcfaLabelVisitor<Map<VarDecl<?>, Set<VarDecl<?>>>, Void> {

    @Override
    public Void visit(SkipStmt stmt, Map<VarDecl<?>, Set<VarDecl<?>>> param) {
        return null;
    }

    @Override
    public Void visit(AssumeStmt stmt, Map<VarDecl<?>, Set<VarDecl<?>>> param) {
        return null;
    }

    @Override
    public <DeclType extends Type> Void visit(AssignStmt<DeclType> stmt, Map<VarDecl<?>, Set<VarDecl<?>>> param) {
        Set<VarDecl<?>> dependencies = ExprUtils.getVars(stmt.getExpr()).stream().map(o -> param.getOrDefault(o, Set.of(o))).reduce(Sets::union).orElse(Set.of());
        param.put(stmt.getVarDecl(), Sets.union(dependencies, Set.of(stmt.getVarDecl())));
        return null;
    }

    @Override
    public <DeclType extends Type> Void visit(HavocStmt<DeclType> stmt, Map<VarDecl<?>, Set<VarDecl<?>>> param) {
        param.put(stmt.getVarDecl(), Set.of(stmt.getVarDecl()));
        return null;
    }

    @Override
    public Void visit(SequenceStmt stmt, Map<VarDecl<?>, Set<VarDecl<?>>> param) {
        for (Stmt stmtStmt : stmt.getStmts()) {
            stmtStmt.accept(this, param);
        }
        return null;
    }

    @Override
    public Void visit(NonDetStmt stmt, Map<VarDecl<?>, Set<VarDecl<?>>> param) {
        throw new UnsupportedOperationException("NonDetStmts cannot have dependencies");
    }

    @Override
    public Void visit(OrtStmt stmt, Map<VarDecl<?>, Set<VarDecl<?>>> param) {
        throw new UnsupportedOperationException("OrtStmts cannot have dependencies");
    }

    @Override
    public Void visit(LoopStmt stmt, Map<VarDecl<?>, Set<VarDecl<?>>> param) {
        throw new UnsupportedOperationException("loopstmts cannot have dependencies");
    }

    @Override
    public Void visit(IfStmt stmt, Map<VarDecl<?>, Set<VarDecl<?>>> param) {
        throw new UnsupportedOperationException("IfStmts cannot have dependencies");
    }

    @Override
    public Void visit(XcfaLabel.AtomicBeginXcfaLabel label, Map<VarDecl<?>, Set<VarDecl<?>>> param) {
        return null;
    }

    @Override
    public Void visit(XcfaLabel.AtomicEndXcfaLabel label, Map<VarDecl<?>, Set<VarDecl<?>>> param) {
        return null;
    }

    @Override
    public Void visit(XcfaLabel.ProcedureCallXcfaLabel label, Map<VarDecl<?>, Set<VarDecl<?>>> param) {
        throw new UnsupportedOperationException("ProcedureCallXcfaLabels cannot have dependencies");
    }

    @Override
    public Void visit(XcfaLabel.StartThreadXcfaLabel label, Map<VarDecl<?>, Set<VarDecl<?>>> param) {
        throw new UnsupportedOperationException("StartThreadXcfaLabel cannot have dependencies");
    }

    @Override
    public Void visit(XcfaLabel.JoinThreadXcfaLabel label, Map<VarDecl<?>, Set<VarDecl<?>>> param) {
        throw new UnsupportedOperationException("JoinThreadXcfaLabel cannot have dependencies");
    }

    @Override
    public <T extends Type> Void visit(XcfaLabel.LoadXcfaLabel<T> label, Map<VarDecl<?>, Set<VarDecl<?>>> param) {
        param.put(label.getLocal(), Set.of(label.getLocal()));
        return null;
    }

    @Override
    public <T extends Type> Void visit(XcfaLabel.StoreXcfaLabel<T> label, Map<VarDecl<?>, Set<VarDecl<?>>> param) {
        return null;
    }

    @Override
    public Void visit(XcfaLabel.FenceXcfaLabel label, Map<VarDecl<?>, Set<VarDecl<?>>> param) {
        return null;
    }

    @Override
    public Void visit(XcfaLabel.StmtXcfaLabel label, Map<VarDecl<?>, Set<VarDecl<?>>> param) {
        label.getStmt().accept(this, param);
        return null;
    }

    @Override
    public Void visit(XcfaLabel.SequenceLabel sequenceLabel, Map<VarDecl<?>, Set<VarDecl<?>>> param) {
        for (XcfaLabel label : sequenceLabel.getLabels()) {
            label.accept(this, param);
        }
        return null;
    }

    @Override
    public Void visit(XcfaLabel.NondetLabel nondetLabel, Map<VarDecl<?>, Set<VarDecl<?>>> param) {
        throw new UnsupportedOperationException("NondetLabels cannot have dependencies");
    }
}
