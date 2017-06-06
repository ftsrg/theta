package hu.bme.mit.theta.core.type.abstracttype;

import java.util.Collection;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.type.anytype.IteExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public final class AbstractExprs {

	private AbstractExprs() {
	}

	public static IteExpr<?> Ite(final Expr<BoolType> cond, final Expr<?> then, final Expr<?> elze) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	public static AddExpr<?> Add(final Collection<? extends Expr<?>> ops) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	public static SubExpr<?> Sub(final Expr<?> leftOp, final Expr<?> rightOp) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	public static NegExpr<?> Neg(final Expr<?> op) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	public static MulExpr<?> Mul(final Collection<? extends Expr<?>> ops) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	public static DivExpr<?> Div(final Expr<?> leftOp, final Expr<?> rightOp) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	public static EqExpr<?> Eq(final Expr<?> leftOp, final Expr<?> rightOp) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	public static NeqExpr<?> Neq(final Expr<?> leftOp, final Expr<?> rightOp) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	public static LtExpr<?> Lt(final Expr<?> leftOp, final Expr<?> rightOp) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	public static LeqExpr<?> Leq(final Expr<?> leftOp, final Expr<?> rightOp) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	public static GtExpr<?> Gt(final Expr<?> leftOp, final Expr<?> rightOp) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	public static GeqExpr<?> Geq(final Expr<?> leftOp, final Expr<?> rightOp) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	/*
	 * Convenience methods
	 */

	public static AddExpr<?> Add(final Expr<?> op1, final Expr<?> op2) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	public static MulExpr<?> Mul(final Expr<?> op1, final Expr<?> op2) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

}
