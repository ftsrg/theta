package hu.bme.mit.inf.theta.formalism.utils.impl;

import java.util.Collection;

import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.type.BoolType;
import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.core.utils.impl.AtomCollectorVisitor;
import hu.bme.mit.inf.theta.formalism.common.expr.ClockRefExpr;
import hu.bme.mit.inf.theta.formalism.common.expr.PrimedExpr;
import hu.bme.mit.inf.theta.formalism.common.expr.ProcCallExpr;
import hu.bme.mit.inf.theta.formalism.common.expr.ProcRefExpr;
import hu.bme.mit.inf.theta.formalism.common.expr.VarRefExpr;
import hu.bme.mit.inf.theta.formalism.utils.FormalismExprVisitor;

public class FormalismAtomCollectorVisitor extends AtomCollectorVisitor
		implements FormalismExprVisitor<Collection<Expr<? extends BoolType>>, Void> {

	@Override
	public <ExprType extends Type> Void visit(final PrimedExpr<ExprType> expr,
			final Collection<Expr<? extends BoolType>> param) {
		return visitNonBoolConnective(expr, param);
	}

	@Override
	public <ReturnType extends Type> Void visit(final ProcCallExpr<ReturnType> expr,
			final Collection<Expr<? extends BoolType>> param) {
		return visitNonBoolConnective(expr, param);
	}

	@Override
	public <ReturnType extends Type> Void visit(final ProcRefExpr<ReturnType> expr,
			final Collection<Expr<? extends BoolType>> param) {
		return visitNonBoolConnective(expr, param);
	}

	@Override
	public <DeclType extends Type> Void visit(final VarRefExpr<DeclType> expr,
			final Collection<Expr<? extends BoolType>> param) {
		return visitNonBoolConnective(expr, param);
	}

	@Override
	public Void visit(final ClockRefExpr expr, final Collection<Expr<? extends BoolType>> param) {
		return visitNonBoolConnective(expr, param);
	}

}
