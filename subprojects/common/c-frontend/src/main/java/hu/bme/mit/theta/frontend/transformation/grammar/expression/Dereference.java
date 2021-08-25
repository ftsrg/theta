package hu.bme.mit.theta.frontend.transformation.grammar.expression;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.UnaryExpr;

public class Dereference<R extends Type, T extends Type> extends UnaryExpr<R, T> {
	private static final int HASH_SEED = 6988;
	private static final String label = "*";
	private final T type;

	private Dereference(Expr<R> op, T type) {
		super(op);
		this.type = type;
	}

	public static <R extends Type, T extends Type> Dereference<R, T> of(Expr<R> op, T type) {
		return new Dereference<>(op, type);
	}

	@Override
	public T getType() {
		return type;
	}

	@Override
	public LitExpr<T> eval(Valuation val) {
		throw new IllegalStateException("Reference/Dereference expressions are not meant to be evaluated!");
	}

	@Override
	public UnaryExpr<R, T> with(Expr<R> op) {
		return of(op, type);
	}

	@Override
	protected int getHashSeed() {
		return HASH_SEED;
	}

	@Override
	public String getOperatorLabel() {
		return label;
	}
}
