package hu.bme.mit.theta.formalism.tcfa.dsl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.stmt.impl.Stmts.Assign;
import static hu.bme.mit.theta.core.stmt.impl.Stmts.Assume;

import java.util.Optional;

import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.dsl.DeclSymbol;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.VarRefExpr;
import hu.bme.mit.theta.core.model.Assignment;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.impl.ExprUtils;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslBaseVisitor;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslParser.AssignStmtContext;
import hu.bme.mit.theta.formalism.tcfa.dsl.gen.TcfaDslParser.AssumeStmtContext;

public class TcfaStmtCreatorVisitor extends TcfaDslBaseVisitor<Stmt> {

	final Scope scope;
	final Assignment assignment;

	public TcfaStmtCreatorVisitor(final Scope scope, final Assignment assignment) {
		this.scope = checkNotNull(scope);
		this.assignment = checkNotNull(assignment);
	}

	@SuppressWarnings("unchecked")
	@Override
	public Stmt visitAssignStmt(final AssignStmtContext ctx) {
		final Optional<? extends Symbol> optLhsSymbol = scope.resolve(ctx.lhs.getText());
		checkArgument(optLhsSymbol.isPresent());
		final Symbol lhsSymbol = optLhsSymbol.get();
		checkArgument(lhsSymbol instanceof DeclSymbol);
		final DeclSymbol declSymbol = (DeclSymbol) lhsSymbol;
		final Decl<?> decl = declSymbol.getDecl();

		final VarDecl<Type> lhs;
		if (decl instanceof VarDecl) {
			lhs = (VarDecl<Type>) decl;
		} else if (decl instanceof TcfaParamDecl) {
			final VarRefExpr<Type> varRef = (VarRefExpr<Type>) assignment.eval(decl).get();
			lhs = varRef.getDecl();
		} else {
			throw new AssertionError();
		}
		final Expr<? extends Type> value = TcfaDslHelper.createExpr(scope, assignment, ctx.value);
		return Assign(lhs, ExprUtils.simplify(value));
	}

	@Override
	public AssumeStmt visitAssumeStmt(final AssumeStmtContext ctx) {
		final Expr<? extends BoolType> cond = TcfaDslHelper.createBoolExpr(scope, assignment, ctx.cond);
		return Assume(ExprUtils.simplify(cond));
	}

}
