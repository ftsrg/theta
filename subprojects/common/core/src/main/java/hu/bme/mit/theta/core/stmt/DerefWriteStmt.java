package hu.bme.mit.theta.core.stmt;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.RefExpr;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public final class DerefWriteStmt<DeclType extends Type> implements Stmt {
	private static final String STMT_LABEL = "derefassign";

	private final RefExpr<DeclType> ref;
	private final Expr<DeclType> expr;

	private DerefWriteStmt(final RefExpr<DeclType> lhs, final Expr<DeclType> expr) {
		this.ref = checkNotNull(lhs);
		this.expr = checkNotNull(expr);
	}

	public static <DeclType extends Type> DerefWriteStmt<DeclType> of(final RefExpr<DeclType> lhs, final Expr<DeclType> rhs) {
		return new DerefWriteStmt<>(lhs, rhs);
	}

	public static <DeclType extends Type> DerefWriteStmt<DeclType> create(final RefExpr<?> lhs, final Expr<?> rhs) {
		@SuppressWarnings("unchecked") final RefExpr<DeclType> newLhs = (RefExpr<DeclType>) lhs;
		final Expr<DeclType> newRhs = cast(rhs, newLhs.getType());
		return DerefWriteStmt.of(newLhs, newRhs);
	}

	public RefExpr<DeclType> getRef() {
		return ref;
	}

	public Expr<DeclType> getExpr() {
		return expr;
	}

	@Override
	public String toString() {
		return STMT_LABEL + "(" + ref + ", " + expr + ")";
	}

	@Override
	public <P, R> R accept(final StmtVisitor<? super P, ? extends R> visitor, final P param) {
		throw new UnsupportedOperationException();
	}

}
