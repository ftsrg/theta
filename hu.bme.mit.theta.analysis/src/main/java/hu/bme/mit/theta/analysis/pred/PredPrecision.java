package hu.bme.mit.theta.analysis.pred;

import java.util.Collection;

import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.expr.ExprStates;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.solver.Solver;

public interface PredPrecision extends Precision {

	PredState createState(final Valuation valuation);

	default Collection<? extends PredState> createStates(final Solver solver, final Expr<? extends BoolType> expr) {
		return ExprStates.createStates(solver, expr, this::createState);
	}
}
