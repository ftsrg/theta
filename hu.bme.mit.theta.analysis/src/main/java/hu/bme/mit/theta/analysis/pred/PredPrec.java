package hu.bme.mit.theta.analysis.pred;

import java.util.Collection;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.expr.ExprStates;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.Solver;

public interface PredPrec extends Prec {

	PredState createState(final Valuation valuation);

	default Collection<? extends PredState> createStatesForExpr(final Solver solver, final Expr<BoolType> expr) {
		return ExprStates.createStatesForExpr(solver, expr, this::createState);
	}
}
