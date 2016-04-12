package hu.bme.mit.inf.ttmc.constraint.z3.solver;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Map;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.solver.Interpolant;
import hu.bme.mit.inf.ttmc.core.solver.ItpMarker;
import hu.bme.mit.inf.ttmc.core.type.BoolType;

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
