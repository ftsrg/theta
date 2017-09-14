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

import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.Arrays.asList;

import java.util.List;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public class Stmts {

	private static final SkipStmt SKIP_STMT;

	static {
		SKIP_STMT = new SkipStmt();
	}

	protected Stmts() {
	}

	public static <T extends Type> DeclStmt<T> Decl(final VarDecl<T> varDecl) {
		checkNotNull(varDecl);
		return new DeclStmt<>(varDecl);
	}

	public static <T extends Type> DeclStmt<T> Decl(final VarDecl<T> varDecl, final Expr<T> initVal) {
		checkNotNull(varDecl);
		checkNotNull(initVal);
		return new DeclStmt<>(varDecl, initVal);
	}

	public static AssumeStmt Assume(final Expr<BoolType> cond) {
		checkNotNull(cond);
		return new AssumeStmt(cond);
	}

	public static AssertStmt Assert(final Expr<BoolType> cond) {
		checkNotNull(cond);
		return new AssertStmt(cond);
	}

	public static <T extends Type> AssignStmt<T> Assign(final VarDecl<T> lhs, final Expr<T> rhs) {
		checkNotNull(lhs);
		checkNotNull(rhs);
		return new AssignStmt<>(lhs, rhs);
	}

	public static <T extends Type> HavocStmt<T> Havoc(final VarDecl<T> varDecl) {
		checkNotNull(varDecl);
		return new HavocStmt<>(varDecl);
	}

	public static BlockStmt Block(final List<? extends Stmt> stmts) {
		checkNotNull(stmts);
		return new BlockStmt(stmts);
	}

	public static BlockStmt Block(final Stmt... stmts) {
		return Block(asList(stmts));
	}

	public static <T extends Type> ReturnStmt<T> Return(final Expr<T> expr) {
		checkNotNull(expr);
		return new ReturnStmt<>(expr);
	}

	public static IfStmt If(final Expr<BoolType> cond, final Stmt then) {
		checkNotNull(cond);
		checkNotNull(then);
		return new IfStmt(cond, then);
	}

	public static IfElseStmt If(final Expr<BoolType> cond, final Stmt then, final Stmt elze) {
		checkNotNull(cond);
		checkNotNull(then);
		checkNotNull(elze);
		return new IfElseStmt(cond, then, elze);
	}

	public static WhileStmt While(final Expr<BoolType> cond, final Stmt stmt) {
		checkNotNull(cond);
		checkNotNull(stmt);
		return new WhileStmt(cond, stmt);
	}

	public static DoStmt Do(final Stmt stmt, final Expr<BoolType> cond) {
		checkNotNull(stmt);
		checkNotNull(cond);
		return new DoStmt(stmt, cond);
	}

	public static SkipStmt Skip() {
		return SKIP_STMT;
	}

}
