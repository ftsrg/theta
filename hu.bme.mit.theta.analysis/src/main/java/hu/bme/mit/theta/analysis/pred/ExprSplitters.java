package hu.bme.mit.theta.analysis.pred;

import java.util.Collection;
import java.util.Collections;
import java.util.function.Function;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.utils.impl.ExprUtils;

public class ExprSplitters {
	public interface ExprSplitter extends Function<Expr<? extends BoolType>, Collection<Expr<? extends BoolType>>> {
	}

	public static ExprSplitter whole() {
		return new Whole();
	}

	public static ExprSplitter conjuncts() {
		return new Conjuncts();
	}

	public static ExprSplitter atoms() {
		return new Atoms();
	}

	private static final class Whole implements ExprSplitter {
		@Override
		public Collection<Expr<? extends BoolType>> apply(final Expr<? extends BoolType> expr) {
			return Collections.singleton(expr);
		}

		@Override
		public String toString() {
			return getClass().getSimpleName();
		}
	}

	private static final class Conjuncts implements ExprSplitter {
		@Override
		public Collection<Expr<? extends BoolType>> apply(final Expr<? extends BoolType> expr) {
			return ExprUtils.getConjuncts(expr);
		}

		@Override
		public String toString() {
			return getClass().getSimpleName();
		}
	}

	private static final class Atoms implements ExprSplitter {
		@Override
		public Collection<Expr<? extends BoolType>> apply(final Expr<? extends BoolType> expr) {
			return ExprUtils.getAtoms(expr);
		}

		@Override
		public String toString() {
			return getClass().getSimpleName();
		}
	}
}
