package hu.bme.mit.theta.formalism.xta.dsl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.Exprs;
import hu.bme.mit.theta.core.expr.VarRefExpr;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.Stmts;
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.formalism.xta.dsl.XtaExpression.ExpressionInstantiationVisitor;
import hu.bme.mit.theta.formalism.xta.dsl.gen.XtaDslBaseVisitor;
import hu.bme.mit.theta.formalism.xta.dsl.gen.XtaDslParser.AssignmentExpressionContext;
import hu.bme.mit.theta.formalism.xta.dsl.gen.XtaDslParser.AssignmentOpContext;
import hu.bme.mit.theta.formalism.xta.dsl.gen.XtaDslParser.ExpressionContext;
import hu.bme.mit.theta.formalism.xta.dsl.gen.XtaDslParser.PostfixExpressionContext;
import hu.bme.mit.theta.formalism.xta.dsl.gen.XtaDslParser.PostfixOpContext;

final class XtaUpdate {
	private final Scope scope;
	private final ExpressionContext context;

	public XtaUpdate(final Scope scope, final ExpressionContext context) {
		this.scope = checkNotNull(scope);
		this.context = checkNotNull(context);
	}

	public AssignStmt<?, ?> instantiate(final Environment env) {
		final UpdateInstantiationVisitor visitor = new UpdateInstantiationVisitor(env);
		final AssignStmt<?, ?> result = context.accept(visitor);
		return result;
	}

	private final class UpdateInstantiationVisitor extends XtaDslBaseVisitor<AssignStmt<?, ?>> {
		private final ExpressionInstantiationVisitor visitor;

		public UpdateInstantiationVisitor(final Environment env) {
			visitor = new ExpressionInstantiationVisitor(scope, env);
		}

		@Override
		public AssignStmt<?, ?> visitAssignmentExpression(final AssignmentExpressionContext ctx) {
			if (ctx.fOper == null) {
				return visitChildren(ctx);
			} else {
				@SuppressWarnings("unchecked")
				final VarRefExpr<Type> leftOp = (VarRefExpr<Type>) ctx.fLeftOp.accept(visitor);
				final VarDecl<Type> varDecl = leftOp.getDecl();
				@SuppressWarnings("unchecked")
				final Expr<Type> rightOp = (Expr<Type>) ctx.fRightOp.accept(visitor);

				final AssignmentOpContext op = ctx.fOper;
				if (op.fAssignOp != null) {
					return Stmts.Assign(varDecl, rightOp);
				} else {
					// TODO Auto-generated method stub
					throw new UnsupportedOperationException();
				}
			}
		}

		@Override
		@SuppressWarnings("unchecked")
		public AssignStmt<?, ?> visitPostfixExpression(final PostfixExpressionContext ctx) {
			if (ctx.fOpers == null || ctx.fOpers.isEmpty()) {
				return visitChildren(ctx);
			} else {
				final VarRefExpr<? extends Type> leftOp = (VarRefExpr<Type>) ctx.fOp.accept(visitor);
				final VarDecl<Type> varDecl = (VarDecl<Type>) leftOp.getDecl();

				final PostfixOpContext op = Utils.singleElementOf(ctx.fOpers);
				if (op.fPostIncOp != null) {
					return Stmts.Assign(varDecl, Exprs.Add((Expr<IntType>) leftOp, Exprs.Int(1)));
				} else if (op.fPostDeclOp != null) {
					return Stmts.Assign(varDecl, Exprs.Sub((Expr<IntType>) leftOp, Exprs.Int(1)));
				} else {
					throw new UnsupportedOperationException();
				}
			}
		}
	}

}
