package hu.bme.mit.theta.formalism.xta;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.core.expr.Expr;

public final class SyncLabel {

	public static enum Kind {
		EMIT, RECEIVE
	}

	private final Expr<ChanType> expr;
	private final Kind kind;

	private SyncLabel(final Expr<ChanType> expr, final Kind kind) {
		this.expr = checkNotNull(expr);
		this.kind = checkNotNull(kind);
	}

	public static SyncLabel emit(final Expr<ChanType> expr) {
		return new SyncLabel(expr, Kind.EMIT);
	}

	public static SyncLabel receive(final Expr<ChanType> expr) {
		return new SyncLabel(expr, Kind.RECEIVE);
	}

	public Expr<ChanType> getExpr() {
		return expr;
	}

	public Kind getKind() {
		return kind;
	}

	@Override
	public int hashCode() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public boolean equals(final Object obj) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public String toString() {
		return kind == Kind.EMIT ? expr + "!" : expr + "?";
	}

}
