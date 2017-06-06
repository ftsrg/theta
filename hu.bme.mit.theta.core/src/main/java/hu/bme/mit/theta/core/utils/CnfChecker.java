package hu.bme.mit.theta.core.utils;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.type.anytype.IteExpr;
import hu.bme.mit.theta.core.type.anytype.PrimeExpr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.booltype.AndExpr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.IffExpr;
import hu.bme.mit.theta.core.type.booltype.ImplyExpr;
import hu.bme.mit.theta.core.type.booltype.NotExpr;
import hu.bme.mit.theta.core.type.booltype.OrExpr;

final class CnfChecker {

	private static enum CnfStatus {
		START(0), INSIDE_AND(1), INSIDE_OR(2), INSIDE_NOT(3);
		private final int value;

		private CnfStatus(final int value) {
			this.value = value;
		}

		public int getValue() {
			return value;
		}
	}

	public static boolean isCnf(final Expr<BoolType> expr) {
		return isCnf(expr, CnfStatus.START);
	}

	private static boolean isCnf(final Expr<BoolType> expr, final CnfStatus status) {
		if (expr instanceof BoolLitExpr) {
			return true;

		} else if (expr instanceof NotExpr) {
			final NotExpr notExpr = (NotExpr) expr;
			// NOT is not allowed inside NOT
			if (status.getValue() >= CnfStatus.INSIDE_NOT.getValue()) {
				return false;
			} else {
				return isCnf(notExpr.getOp(), CnfStatus.INSIDE_NOT);
			}

		} else if (expr instanceof AndExpr) {
			final AndExpr andExpr = (AndExpr) expr;
			// AND is allowed inside AND
			if (status.getValue() > CnfStatus.INSIDE_AND.getValue()) {
				return false;
			} else {
				return andExpr.getOps().stream().allMatch(op -> isCnf(op, CnfStatus.INSIDE_AND));
			}

		} else if (expr instanceof OrExpr) {
			final OrExpr orExpr = (OrExpr) expr;
			// OR is allowed inside OR
			if (status.getValue() > CnfStatus.INSIDE_OR.getValue()) {
				return false;
			} else {
				return orExpr.getOps().stream().allMatch(op -> isCnf(op, CnfStatus.INSIDE_OR));
			}

		} else if (expr instanceof ImplyExpr) {
			return false;

		} else if (expr instanceof IffExpr) {
			return false;

		} else if (expr instanceof RefExpr) {
			return true;

		} else if (expr instanceof PrimeExpr) {
			final PrimeExpr<BoolType> primeExpr = (PrimeExpr<BoolType>) expr;
			return isCnf(primeExpr.getOp(), CnfStatus.INSIDE_NOT);

		} else if (expr instanceof IteExpr) {
			return false;

		} else {
			return true;
		}
	}
}
