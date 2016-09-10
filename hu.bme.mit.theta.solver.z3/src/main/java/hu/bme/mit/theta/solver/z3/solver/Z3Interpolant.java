package hu.bme.mit.theta.solver.z3.solver;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Map;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.solver.Interpolant;
import hu.bme.mit.theta.solver.ItpMarker;

public class Z3Interpolant implements Interpolant {

	private final Map<ItpMarker, Expr<BoolType>> itpMap;

	Z3Interpolant(final Map<ItpMarker, Expr<BoolType>> itpMap) {
		this.itpMap = itpMap;
	}

	@Override
	public Expr<BoolType> eval(final ItpMarker marker) {
		checkNotNull(marker);
		final Expr<BoolType> itpExpr = itpMap.get(marker);
		checkNotNull(itpExpr);
		return itpExpr;
	}

}
