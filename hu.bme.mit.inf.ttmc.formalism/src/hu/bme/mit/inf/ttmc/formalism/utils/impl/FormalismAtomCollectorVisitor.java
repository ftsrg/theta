package hu.bme.mit.inf.ttmc.formalism.utils.impl;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.AtomCollectorVisitor;
import hu.bme.mit.inf.ttmc.formalism.common.expr.PrimedExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.ProcCallExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.ProcRefExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.VarRefExpr;
import hu.bme.mit.inf.ttmc.formalism.utils.FormalismExprVisitor;

public class FormalismAtomCollectorVisitor extends AtomCollectorVisitor implements FormalismExprVisitor<Collection<Expr<? extends BoolType>>, Void> {

	@Override
	public <ExprType extends Type> Void visit(final PrimedExpr<ExprType> expr, final Collection<Expr<? extends BoolType>> param) {
		return visitNonBoolConnective(expr, param);
	}

	@Override
	public <ReturnType extends Type> Void visit(final ProcCallExpr<ReturnType> expr, final Collection<Expr<? extends BoolType>> param) {
		return visitNonBoolConnective(expr, param);
	}

	@Override
	public <ReturnType extends Type> Void visit(final ProcRefExpr<ReturnType> expr, final Collection<Expr<? extends BoolType>> param) {
		return visitNonBoolConnective(expr, param);
	}

	@Override
	public <DeclType extends Type> Void visit(final VarRefExpr<DeclType> expr, final Collection<Expr<? extends BoolType>> param) {
		return visitNonBoolConnective(expr, param);
	}

}
