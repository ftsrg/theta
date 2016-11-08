package hu.bme.mit.theta.solver.utils;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Not;

import java.util.Iterator;
import java.util.function.Function;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.model.Model;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverFactory;

public final class SolverUtils {

	private SolverUtils() {
	}

	public static <S extends Solver, R> R using(final S solver, final Function<? super S, ? extends R> function) {
		solver.push();
		final R result = function.apply(solver);
		solver.pop();
		return result;
	}

	public static boolean entails(final Solver solver, final Iterable<? extends Expr<? extends BoolType>> antecedents,
			final Iterable<? extends Expr<? extends BoolType>> consequents) {
		checkNotNull(solver);
		checkNotNull(antecedents);
		checkNotNull(consequents);
		return using(solver, s -> {
			antecedents.forEach(antecedent -> s.add(antecedent));
			consequents.forEach(consequent -> s.add(Not(consequent)));
			return s.check().isUnsat();
		});
	}

	public static Stream<Model> models(final SolverFactory factory, final Expr<? extends BoolType> expr) {
		return models(factory, expr, m -> Not(m.toExpr()));
	}

	public static Stream<Model> models(final SolverFactory factory, final Expr<? extends BoolType> expr,
			final Function<? super Model, ? extends Expr<? extends BoolType>> feedback) {
		final Iterable<Model> iterable = () -> new ModelIterator(factory, expr, feedback);
		return StreamSupport.stream(iterable.spliterator(), false);
	}

	private static final class ModelIterator implements Iterator<Model> {
		private final Solver solver;
		private final Function<? super Model, ? extends Expr<? extends BoolType>> feedback;

		private ModelIterator(final SolverFactory factory, final Expr<? extends BoolType> expr,
				final Function<? super Model, ? extends Expr<? extends BoolType>> feedback) {
			checkNotNull(expr);
			checkNotNull(factory);
			this.feedback = checkNotNull(feedback);

			solver = factory.createSolver();
			solver.add(expr);
		}

		@Override
		public boolean hasNext() {
			return solver.check().isSat();
		}

		@Override
		public Model next() {
			final Model model = solver.getModel();
			solver.add(feedback.apply(model));
			return model;
		}
	}

}
