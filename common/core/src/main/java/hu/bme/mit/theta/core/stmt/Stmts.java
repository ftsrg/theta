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
package hu.bme.mit.theta.core.stmt;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;

import java.util.List;

/**
 * Factory class to instantiate different statements.
 *
 * @see Stmt
 */
public final class Stmts {

	private Stmts() {
	}

	public static SkipStmt Skip() {
		return SkipStmt.getInstance();
	}

	public static AssumeStmt Assume(final Expr<BoolType> cond) {
		return AssumeStmt.of(cond);
	}

	public static <T extends Type> AssignStmt<T> Assign(final VarDecl<T> lhs, final Expr<T> rhs) {
		return AssignStmt.of(lhs, rhs);
	}

	public static <T extends Type> HavocStmt<T> Havoc(final VarDecl<T> varDecl) {
		return HavocStmt.of(varDecl);
	}

	public static SequenceStmt SequenceStmt(final List<Stmt> stmts) {
		return SequenceStmt.of(stmts);
	}

	public static NonDetStmt NonDetStmt(final List<Stmt> stmts) {
		return NonDetStmt.of(stmts);
	}

}
