/*
 * Copyright 2021 Budapest University of Technology and Economics
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package hu.bme.mit.theta.xcfa.model.utils;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.stmt.IfStmt;
import hu.bme.mit.theta.core.stmt.LoopStmt;
import hu.bme.mit.theta.core.stmt.NonDetStmt;
import hu.bme.mit.theta.core.stmt.OrtStmt;
import hu.bme.mit.theta.core.stmt.PopStmt;
import hu.bme.mit.theta.core.stmt.PushStmt;
import hu.bme.mit.theta.core.stmt.SequenceStmt;
import hu.bme.mit.theta.core.stmt.SkipStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaLabelVisitor;

import java.util.Set;

// LhsVars, RhsVars
public class XcfaLabelVarCollector implements XcfaLabelVisitor<Tuple2<Set<VarDecl<?>>, Set<VarDecl<?>>>, Void> {

    @Override
    public Void visit(SkipStmt stmt, Tuple2<Set<VarDecl<?>>, Set<VarDecl<?>>> param) {
        return null;
    }

    @Override
    public Void visit(AssumeStmt stmt, Tuple2<Set<VarDecl<?>>, Set<VarDecl<?>>> param) {
        param.get2().addAll(StmtUtils.getVars(stmt));
        return null;
    }

    @Override
    public <DeclType extends Type> Void visit(AssignStmt<DeclType> stmt, Tuple2<Set<VarDecl<?>>, Set<VarDecl<?>>> param) {
        param.get2().addAll(ExprUtils.getVars(stmt.getExpr()));
        param.get1().add(stmt.getVarDecl());
        return null;
    }

    @Override
    public <DeclType extends Type> Void visit(HavocStmt<DeclType> stmt, Tuple2<Set<VarDecl<?>>, Set<VarDecl<?>>> param) {
        param.get1().add(stmt.getVarDecl());
        return null;
    }

    @Override
    public Void visit(SequenceStmt stmt, Tuple2<Set<VarDecl<?>>, Set<VarDecl<?>>> param) {
        for (Stmt stmtStmt : stmt.getStmts()) {
            stmtStmt.accept(this, param);
        }
        return null;
    }

    @Override
    public Void visit(NonDetStmt stmt, Tuple2<Set<VarDecl<?>>, Set<VarDecl<?>>> param) {
        for (Stmt stmtStmt : stmt.getStmts()) {
            stmtStmt.accept(this, param);
        }
        return null;
    }

    @Override
    public Void visit(OrtStmt stmt, Tuple2<Set<VarDecl<?>>, Set<VarDecl<?>>> param) {
        for (Stmt stmtStmt : stmt.getStmts()) {
            stmtStmt.accept(this, param);
        }
        return null;
    }

    @Override
    public Void visit(LoopStmt stmt, Tuple2<Set<VarDecl<?>>, Set<VarDecl<?>>> param) {
        throw new UnsupportedOperationException("Not yet implemented!");
    }

    @Override
    public <DeclType extends Type> Void visit(PushStmt<DeclType> stmt, Tuple2<Set<VarDecl<?>>, Set<VarDecl<?>>> param) {
        throw new UnsupportedOperationException("Not yet implemented!");
    }

    @Override
    public <DeclType extends Type> Void visit(PopStmt<DeclType> stmt, Tuple2<Set<VarDecl<?>>, Set<VarDecl<?>>> param) {
        throw new UnsupportedOperationException("Not yet implemented!");
    }

    @Override
    public Void visit(IfStmt stmt, Tuple2<Set<VarDecl<?>>, Set<VarDecl<?>>> param) {
        throw new UnsupportedOperationException("Not yet implemented!");
    }

    @Override
    public Void visit(XcfaLabel.AtomicBeginXcfaLabel label, Tuple2<Set<VarDecl<?>>, Set<VarDecl<?>>> param) {
        return null;
    }

    @Override
    public Void visit(XcfaLabel.AtomicEndXcfaLabel label, Tuple2<Set<VarDecl<?>>, Set<VarDecl<?>>> param) {
        return null;
    }

    @Override
    public Void visit(XcfaLabel.ProcedureCallXcfaLabel label, Tuple2<Set<VarDecl<?>>, Set<VarDecl<?>>> param) {
        for (Expr<?> labelParam : label.getParams()) {
            if(labelParam instanceof RefExpr) {
                param.get1().add((VarDecl<?>) ((RefExpr<?>) labelParam).getDecl());
            }
            param.get2().addAll(ExprUtils.getVars(labelParam));
        }
        return null;
    }

    @Override
    public Void visit(XcfaLabel.StartThreadXcfaLabel label, Tuple2<Set<VarDecl<?>>, Set<VarDecl<?>>> param) {
        return null;
    }

    @Override
    public Void visit(XcfaLabel.JoinThreadXcfaLabel label, Tuple2<Set<VarDecl<?>>, Set<VarDecl<?>>> param) {
        return null;
    }

    @Override
    public <T extends Type> Void visit(XcfaLabel.LoadXcfaLabel<T> label, Tuple2<Set<VarDecl<?>>, Set<VarDecl<?>>> param) {
        param.get1().add(label.getLocal());
        param.get2().add(label.getGlobal());
        return null;
    }

    @Override
    public <T extends Type> Void visit(XcfaLabel.StoreXcfaLabel<T> label, Tuple2<Set<VarDecl<?>>, Set<VarDecl<?>>> param) {
        param.get2().add(label.getLocal());
        param.get1().add(label.getGlobal());
        return null;
    }

    @Override
    public Void visit(XcfaLabel.FenceXcfaLabel label, Tuple2<Set<VarDecl<?>>, Set<VarDecl<?>>> param) {
        return null;
    }

    @Override
    public Void visit(XcfaLabel.StmtXcfaLabel label, Tuple2<Set<VarDecl<?>>, Set<VarDecl<?>>> param) {
        return label.getStmt().accept(this, param);
    }

    @Override
    public Void visit(XcfaLabel.SequenceLabel sequenceLabel, Tuple2<Set<VarDecl<?>>, Set<VarDecl<?>>> param) {
        for (XcfaLabel label : sequenceLabel.getLabels()) {
            label.accept(this, param);
        }
        return null;
    }

    @Override
    public Void visit(XcfaLabel.NondetLabel nondetLabel, Tuple2<Set<VarDecl<?>>, Set<VarDecl<?>>> param) {
        for (XcfaLabel label : nondetLabel.getLabels()) {
            label.accept(this, param);
        }
        return null;
    }
}
