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

import hu.bme.mit.theta.core.decl.Decl;
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
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.frontend.FrontendMetadata;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaLabelVisitor;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.stmt.Stmts.Assume;
import static hu.bme.mit.theta.core.stmt.Stmts.Havoc;
import static hu.bme.mit.theta.core.stmt.Stmts.NonDetStmt;
import static hu.bme.mit.theta.core.stmt.Stmts.SequenceStmt;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;
import static hu.bme.mit.theta.xcfa.model.XcfaLabel.Load;
import static hu.bme.mit.theta.xcfa.model.XcfaLabel.Sequence;
import static hu.bme.mit.theta.xcfa.model.XcfaLabel.StartThread;
import static hu.bme.mit.theta.xcfa.model.XcfaLabel.Stmt;
import static hu.bme.mit.theta.xcfa.model.XcfaLabel.Store;

public class XcfaLabelVarReplacer implements XcfaLabelVisitor<Map<VarDecl<?>, VarDecl<?>>, XcfaLabel> {

    public static <T extends Type> Expr<T> replaceVars(Expr<T> expr, Map<? extends Decl<?>, ? extends Decl<?>> varLut) {
        if (expr instanceof RefExpr<?>) {
            if (varLut.get(((RefExpr<T>) expr).getDecl()) == null) return expr;
            else {
                Expr<T> tExpr = cast(varLut.get(((RefExpr<T>) expr).getDecl()).getRef(), expr.getType());
                FrontendMetadata.lookupMetadata(expr).forEach((s, o) -> FrontendMetadata.create(tExpr, s, o));
                return tExpr;
            }
        }

        List<? extends Expr<?>> ops = expr.getOps();
        List<Expr<?>> newOps = new ArrayList<>();
        for (Expr<?> op : ops) {
            if (op instanceof LitExpr<?>) newOps.add(op);
            else newOps.add(replaceVars(op, varLut));
        }
        Expr<T> tExpr = expr.withOps(newOps);
        FrontendMetadata.lookupMetadata(expr).forEach((s, o) -> FrontendMetadata.create(tExpr, s, o));
        return tExpr;
    }


    @Override
    public XcfaLabel visit(SkipStmt stmt, Map<VarDecl<?>, VarDecl<?>> param) {
        return Stmt(stmt);
    }

    @Override
    public XcfaLabel visit(AssumeStmt stmt, Map<VarDecl<?>, VarDecl<?>> param) {
        return Stmt(Assume(cast(replaceVars(stmt.getCond(), param), BoolType.getInstance())));
    }

    @Override
    public <DeclType extends Type> XcfaLabel visit(AssignStmt<DeclType> stmt, Map<VarDecl<?>, VarDecl<?>> param) {
        return Stmt(Assign(cast(param.getOrDefault(stmt.getVarDecl(), stmt.getVarDecl()), stmt.getVarDecl().getType()), replaceVars(stmt.getExpr(), param)));
    }

    @Override
    public <DeclType extends Type> XcfaLabel visit(HavocStmt<DeclType> stmt, Map<VarDecl<?>, VarDecl<?>> param) {
        final HavocStmt<?> havoc = Havoc(param.getOrDefault(stmt.getVarDecl(), stmt.getVarDecl()));
        FrontendMetadata.lookupMetadata(stmt).forEach((s, o) -> FrontendMetadata.create(havoc, s, o));
        return Stmt(havoc);
    }

    @Override
    public XcfaLabel visit(SequenceStmt stmt, Map<VarDecl<?>, VarDecl<?>> param) {
        List<Stmt> stmts = stmt.getStmts();
        List<Stmt> newStmts = new ArrayList<>();
        for (Stmt stmt1 : stmts) {
            newStmts.add(stmt1.accept(this, param).getStmt());
        }
        return Stmt(SequenceStmt(newStmts));
    }

    @Override
    public XcfaLabel visit(NonDetStmt stmt, Map<VarDecl<?>, VarDecl<?>> param) {
        List<Stmt> stmts = stmt.getStmts();
        List<Stmt> newStmts = new ArrayList<>();
        for (Stmt stmt1 : stmts) {
            newStmts.add(stmt1.accept(this, param).getStmt());
        }
        return Stmt(NonDetStmt(newStmts));
    }

    @Override
    public XcfaLabel visit(OrtStmt stmt, Map<VarDecl<?>, VarDecl<?>> param) {
        List<Stmt> stmts = stmt.getStmts();
        List<Stmt> newStmts = new ArrayList<>();
        for (Stmt stmt1 : stmts) {
            newStmts.add(stmt1.accept(this, param).getStmt());
        }
        return Stmt(OrtStmt.of(newStmts));
    }

    @Override
    public XcfaLabel visit(LoopStmt stmt, Map<VarDecl<?>, VarDecl<?>> param) {
        throw new UnsupportedOperationException("Not implemented.");
    }

    @Override
    public <DeclType extends Type> XcfaLabel visit(PushStmt<DeclType> stmt, Map<VarDecl<?>, VarDecl<?>> param) {
        throw new UnsupportedOperationException();
    }

    @Override
    public <DeclType extends Type> XcfaLabel visit(PopStmt<DeclType> stmt, Map<VarDecl<?>, VarDecl<?>> param) {
        throw new UnsupportedOperationException();
    }

    @Override
    public XcfaLabel visit(IfStmt stmt, Map<VarDecl<?>, VarDecl<?>> param) {
        throw new UnsupportedOperationException("Not yet implemented!");
    }

    @Override
    public XcfaLabel visit(XcfaLabel.ProcedureCallXcfaLabel label, Map<VarDecl<?>, VarDecl<?>> param) {
        List<Expr<?>> exprs = label.getParams();
        List<Expr<?>> newExprs = new ArrayList<>();
        exprs.forEach((expr) ->
            newExprs.add(replaceVars(expr, param))
        );
        return XcfaLabel.ProcedureCallXcfaLabel.of(newExprs, label.getProcedure());
    }

    @Override
    public <S extends Type> XcfaLabel visit(XcfaLabel.StoreXcfaLabel<S> label, Map<VarDecl<?>, VarDecl<?>> param) {
        return Store(
                param.getOrDefault(label.getLocal(), label.getLocal()),
                param.getOrDefault(label.getGlobal(), label.getGlobal()),
                label.isAtomic(),
                label.getOrdering()
        );
    }

    @Override
    public <S extends Type> XcfaLabel visit(XcfaLabel.LoadXcfaLabel<S> label, Map<VarDecl<?>, VarDecl<?>> param) {
        return Load(
                param.getOrDefault(label.getLocal(), label.getLocal()),
                param.getOrDefault(label.getGlobal(), label.getGlobal()),
                label.isAtomic(),
                label.getOrdering()
        );
    }

    @Override
    public XcfaLabel visit(XcfaLabel.FenceXcfaLabel fenceStmt, Map<VarDecl<?>, VarDecl<?>> param) {
        return fenceStmt;
    }

    @Override
    public XcfaLabel visit(XcfaLabel.StmtXcfaLabel label, Map<VarDecl<?>, VarDecl<?>> param) {
        return label.getStmt().accept(this, param);
    }

    @Override
    public XcfaLabel visit(XcfaLabel.SequenceLabel sequenceLabel, Map<VarDecl<?>, VarDecl<?>> param) {
        return Sequence(sequenceLabel.getLabels().stream().map(label -> label.accept(this, param)).collect(Collectors.toList()));
    }

    @Override
    public XcfaLabel visit(XcfaLabel.NondetLabel nondetLabel, Map<VarDecl<?>, VarDecl<?>> param) {
        return Sequence(nondetLabel.getLabels().stream().map(label -> label.accept(this, param)).collect(Collectors.toList()));
    }

    @Override
    public XcfaLabel visit(XcfaLabel.AtomicBeginXcfaLabel atomicBeginStmt, Map<VarDecl<?>, VarDecl<?>> param) {
        return atomicBeginStmt;
    }

    @Override
    public XcfaLabel visit(XcfaLabel.AtomicEndXcfaLabel atomicEndStmt, Map<VarDecl<?>, VarDecl<?>> param) {
        return atomicEndStmt;
    }

    @Override
    public XcfaLabel visit(XcfaLabel.StartThreadXcfaLabel startThreadStmt, Map<VarDecl<?>, VarDecl<?>> param) {
        return StartThread(startThreadStmt.getKey(), startThreadStmt.getThreadName(), startThreadStmt.getParam() == null ? null : replaceVars(startThreadStmt.getParam(), param));
    }

    @Override
    public XcfaLabel visit(XcfaLabel.JoinThreadXcfaLabel joinThreadStmt, Map<VarDecl<?>, VarDecl<?>> param) {
        return joinThreadStmt;
    }
}
