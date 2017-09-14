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
package hu.bme.mit.theta.core.dsl.impl;

import hu.bme.mit.theta.core.stmt.AssertStmt;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.BlockStmt;
import hu.bme.mit.theta.core.stmt.DeclStmt;
import hu.bme.mit.theta.core.stmt.DoStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.stmt.IfElseStmt;
import hu.bme.mit.theta.core.stmt.IfStmt;
import hu.bme.mit.theta.core.stmt.ReturnStmt;
import hu.bme.mit.theta.core.stmt.SkipStmt;
import hu.bme.mit.theta.core.stmt.WhileStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.StmtVisitor;

public class StmtWriter implements StmtVisitor<Void, String> {

	private static String writeExpr(final Expr<?> expr) {
		return ExprWriter.instance().write(expr);
	}

	@Override
	public String visit(final SkipStmt stmt, final Void param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException();
	}

	@Override
	public <DeclType extends Type> String visit(final DeclStmt<DeclType> stmt, final Void param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException();
	}

	@Override
	public String visit(final AssumeStmt stmt, final Void param) {
		return "assume " + writeExpr(stmt.getCond());
	}

	@Override
	public String visit(final AssertStmt stmt, final Void param) {
		return "assert " + writeExpr(stmt.getCond());
	}

	@Override
	public <DeclType extends Type> String visit(final AssignStmt<DeclType> stmt, final Void param) {
		return stmt.getVarDecl().getName() + " := " + writeExpr(stmt.getExpr());
	}

	@Override
	public <DeclType extends Type> String visit(final HavocStmt<DeclType> stmt, final Void param) {
		return "havoc " + stmt.getVarDecl().getName();
	}

	@Override
	public String visit(final BlockStmt stmt, final Void param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException();
	}

	@Override
	public <ReturnType extends Type> String visit(final ReturnStmt<ReturnType> stmt, final Void param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException();
	}

	@Override
	public String visit(final IfStmt stmt, final Void param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException();
	}

	@Override
	public String visit(final IfElseStmt stmt, final Void param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException();
	}

	@Override
	public String visit(final WhileStmt stmt, final Void param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException();
	}

	@Override
	public String visit(final DoStmt stmt, final Void param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException();
	}

}
