package hu.bme.mit.theta.core.dsl.impl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.stmt.Stmts.Assume;

import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.dsl.DeclSymbol;
import hu.bme.mit.theta.core.dsl.gen.CoreDslBaseVisitor;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.AssignStmtContext;
import hu.bme.mit.theta.core.dsl.gen.CoreDslParser.AssumeStmtContext;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.TypeUtils;

public final class StmtCreatorVisitor extends CoreDslBaseVisitor<Stmt> {

	final Scope scope;

	public StmtCreatorVisitor(final Scope scope) {
		this.scope = checkNotNull(scope);
	}

	@Override
	public Stmt visitAssignStmt(final AssignStmtContext ctx) {
		@SuppressWarnings("unchecked")
		final VarDecl<Type> lhs = (VarDecl<Type>) resolveVar(scope, ctx.lhs.getText());
		final Expr<?> expr = CoreDslHelper.createExpr(scope, ctx.value);
		final Expr<Type> value = TypeUtils.cast(expr, lhs.getType());
		return Assign(lhs, value);
	}

	private VarDecl<?> resolveVar(final Scope scope, final String name) {
		final DeclSymbol declSymbol = CoreDslHelper.resolveDecl(scope, name);
		final Decl<?> decl = declSymbol.getDecl();
		checkArgument(decl instanceof VarDecl);
		final VarDecl<?> varDecl = (VarDecl<?>) decl;
		return varDecl;
	}

	@Override
	public AssumeStmt visitAssumeStmt(final AssumeStmtContext ctx) {
		final Expr<BoolType> cond = CoreDslHelper.createBoolExpr(scope, ctx.cond);
		return Assume(cond);
	}

}
