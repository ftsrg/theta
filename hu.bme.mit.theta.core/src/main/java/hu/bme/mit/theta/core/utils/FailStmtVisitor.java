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
import hu.bme.mit.theta.core.type.Type;

public class FailStmtVisitor<P, R> implements StmtVisitor<P, R> {

	@Override
	public R visit(final SkipStmt stmt, final P param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public <DeclType extends Type> R visit(final DeclStmt<DeclType> stmt, final P param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public R visit(final AssumeStmt stmt, final P param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public R visit(final AssertStmt stmt, final P param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public <DeclType extends Type> R visit(final AssignStmt<DeclType> stmt, final P param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public <LhsType extends Type> R visit(final HavocStmt<LhsType> stmt, final P param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public R visit(final BlockStmt stmt, final P param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public <ReturnType extends Type> R visit(final ReturnStmt<ReturnType> stmt, final P param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public R visit(final IfStmt stmt, final P param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public R visit(final IfElseStmt stmt, final P param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public R visit(final WhileStmt stmt, final P param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public R visit(final DoStmt stmt, final P param) {
		throw new UnsupportedOperationException();
	}

}
