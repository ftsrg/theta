package hu.bme.mit.theta.solver.utils;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Not;

import java.util.Collection;
import java.util.function.Function;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.solver.Solver;

public final class SolverUtils {

	private SolverUtils() {
	}

	public static <S extends Solver, R> R using(final S solver, final Function<? super S, ? extends R> function) {
		solver.push();
		final R result = function.apply(solver);
		solver.pop();
		return result;
	}

	public static boolean entails(final Solver solver, final Collection<? extends Expr<? extends BoolType>> antecedents,
			final Collection<? extends Expr<? extends BoolType>> consequents) {
		checkNotNull(solver);
		checkNotNull(antecedents);
		checkNotNull(consequents);
		return using(solver, s -> {
			antecedents.forEach(antecedent -> solver.add(antecedent));
			consequents.forEach(consequent -> solver.add(Not(consequent)));
			return solver.check().isUnsat();
		});
	}

}
