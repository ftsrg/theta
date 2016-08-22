package hu.bme.mit.inf.ttmc.formalism.tcfa.dsl.impl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.inf.ttmc.formalism.common.stmt.impl.Stmts.Assign;
import static hu.bme.mit.inf.ttmc.formalism.common.stmt.impl.Stmts.Assume;

import hu.bme.mit.inf.ttmc.common.dsl.Scope;
import hu.bme.mit.inf.ttmc.core.decl.Decl;
import hu.bme.mit.inf.ttmc.core.dsl.DeclSymbol;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.model.Assignment;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.AssumeStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;
import hu.bme.mit.inf.ttmc.formalism.tcfa.dsl.gen.TcfaDslBaseVisitor;
import hu.bme.mit.inf.ttmc.formalism.tcfa.dsl.gen.TcfaDslParser.AssignStmtContext;
import hu.bme.mit.inf.ttmc.formalism.tcfa.dsl.gen.TcfaDslParser.AssumeStmtContext;

public class TcfaStmtCreatorVisitor extends TcfaDslBaseVisitor<Stmt> {

	final Scope scope;
	final Assignment assignment;

	public TcfaStmtCreatorVisitor(final Scope scope, final Assignment assignment) {
		this.scope = checkNotNull(scope);
		this.assignment = checkNotNull(assignment);
	}

	@Override
	public Stmt visitAssignStmt(final AssignStmtContext ctx) {
		final VarDecl<Type> lhs = resolveVar(scope, ctx.lhs.getText());
		final Expr<? extends Type> value = TcfaDslHelper.createExpr(scope, assignment, ctx.value);
		return Assign(lhs, value);
	}

	private VarDecl<Type> resolveVar(final Scope scope, final String name) {
		final DeclSymbol declSymbol = TcfaDslHelper.resolveDecl(scope, name);
		final Decl<?, ?> decl = declSymbol.getDecl();
		checkArgument(decl instanceof VarDecl);
		@SuppressWarnings("unchecked")
		final VarDecl<Type> varDecl = (VarDecl<Type>) decl;
		return varDecl;
	}

	@Override
	public AssumeStmt visitAssumeStmt(final AssumeStmtContext ctx) {
		final Expr<? extends BoolType> cond = TcfaDslHelper.createBoolExpr(scope, assignment, ctx.cond);
		return Assume(cond);
	}

}
