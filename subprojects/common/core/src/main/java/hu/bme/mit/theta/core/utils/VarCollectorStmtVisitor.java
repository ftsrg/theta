/*
 *  Copyright 2021 Budapest University of Technology and Economics
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
import hu.bme.mit.theta.core.stmt.StmtVisitor;
import hu.bme.mit.theta.core.type.Type;

import java.util.Collection;

final class VarCollectorStmtVisitor implements StmtVisitor<Collection<VarDecl<?>>, Void> {

	private static final class LazyHolder {
		private final static VarCollectorStmtVisitor INSTANCE = new VarCollectorStmtVisitor();
	}

	private VarCollectorStmtVisitor() {
	}

	static VarCollectorStmtVisitor getInstance() {
		return LazyHolder.INSTANCE;
	}

	@Override
	public Void visit(final SkipStmt stmt, final Collection<VarDecl<?>> vars) {
		return null;
	}

	@Override
	public Void visit(final AssumeStmt stmt, final Collection<VarDecl<?>> vars) {
		ExprUtils.collectVars(stmt.getCond(), vars);
		return null;
	}

	@Override
	public <DeclType extends Type> Void visit(final AssignStmt<DeclType> stmt, final Collection<VarDecl<?>> vars) {
		vars.add(stmt.getVarDecl());
		ExprUtils.collectVars(stmt.getExpr(), vars);
		return null;
	}

	@Override
	public <DeclType extends Type> Void visit(final HavocStmt<DeclType> stmt, final Collection<VarDecl<?>> vars) {
		vars.add(stmt.getVarDecl());
		return null;
	}

	@Override
	public Void visit(SequenceStmt stmt, Collection<VarDecl<?>> vars) {
		for (Stmt subStmt : stmt.getStmts()) {
			subStmt.accept(VarCollectorStmtVisitor.getInstance(), vars);
		}
		return null;
	}

	@Override
	public Void visit(NonDetStmt stmt, Collection<VarDecl<?>> vars) {
		for (Stmt subStmt : stmt.getStmts()) {
			subStmt.accept(VarCollectorStmtVisitor.getInstance(), vars);
		}
		return null;
	}

	@Override
	public Void visit(OrtStmt stmt, Collection<VarDecl<?>> vars) {
		for (Stmt subStmt : stmt.getStmts()) {
			subStmt.accept(VarCollectorStmtVisitor.getInstance(), vars);
		}
		return null;
	}

	@Override
	public Void visit(LoopStmt stmt, Collection<VarDecl<?>> vars) {
		ExprUtils.collectVars(stmt.getFrom(),vars);
		ExprUtils.collectVars(stmt.getTo(),vars);
		vars.add(stmt.getLoopVariable());
		return stmt.getStmt().accept(VarCollectorStmtVisitor.getInstance(),vars);
	}

	@Override
	public <DeclType extends Type> Void visit(PushStmt<DeclType> stmt, Collection<VarDecl<?>> param) {
		param.add(stmt.getVarDecl());
		return null;
	}

	@Override
	public <DeclType extends Type> Void visit(PopStmt<DeclType> stmt, Collection<VarDecl<?>> param) {
		param.add(stmt.getVarDecl());
		return null;
	}

	public Void visit(IfStmt stmt, Collection<VarDecl<?>> vars) {
		ExprUtils.collectVars(stmt.getCond(), vars);
		stmt.getThen().accept(VarCollectorStmtVisitor.getInstance(), vars);
		stmt.getElze().accept(VarCollectorStmtVisitor.getInstance(), vars);
		return null;
	}

}
