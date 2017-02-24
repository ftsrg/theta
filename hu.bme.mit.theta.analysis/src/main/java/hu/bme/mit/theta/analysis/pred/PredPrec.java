package hu.bme.mit.theta.analysis.pred;

import java.util.Collection;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.expr.ExprStates;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.solver.Solver;

public interface PredPrec extends Prec {

	PredState createState(final Valuation valuation);

	default Collection<? extends PredState> createStates(final Solver solver, final Expr<? extends BoolType> expr) {
		return ExprStates.createStates(solver, expr, this::createState);
	}
}
