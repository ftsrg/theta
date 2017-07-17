package hu.bme.mit.theta.solver.utils;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;

import java.util.Iterator;
import java.util.function.Function;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.model.Model;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverFactory;

public final class SolverUtils {

	private SolverUtils() {
	}

	public static boolean entails(final Solver solver, final Iterable<? extends Expr<BoolType>> antecedents,
			final Iterable<? extends Expr<BoolType>> consequents) {
		checkNotNull(solver);
		checkNotNull(antecedents);
		checkNotNull(consequents);
		try (WithPushPop wpp = new WithPushPop(solver)) {
			antecedents.forEach(antecedent -> solver.add(antecedent));
			consequents.forEach(consequent -> solver.add(Not(consequent)));
			return solver.check().isUnsat();
		}
	}

	public static Stream<Model> models(final SolverFactory factory, final Expr<BoolType> expr) {
		return models(factory, expr, m -> Not(m.toExpr()));
	}

	public static Stream<Model> models(final SolverFactory factory, final Expr<BoolType> expr,
			final Function<? super Model, ? extends Expr<BoolType>> feedback) {
		final Iterable<Model> iterable = () -> new ModelIterator(factory, expr, feedback);
		return StreamSupport.stream(iterable.spliterator(), false);
	}

	private static final class ModelIterator implements Iterator<Model> {
		private final Solver solver;
		private final Function<? super Model, ? extends Expr<BoolType>> feedback;

		private ModelIterator(final SolverFactory factory, final Expr<BoolType> expr,
				final Function<? super Model, ? extends Expr<BoolType>> feedback) {
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
