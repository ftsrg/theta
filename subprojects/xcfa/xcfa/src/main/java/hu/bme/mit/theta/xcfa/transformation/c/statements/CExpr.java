package hu.bme.mit.theta.xcfa.transformation.c.statements;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

public class CExpr extends CStatement{
	private final Expr<?> expr;

	public CExpr(Expr<?> expr) {
		this.expr = expr;
	}

	public Expr<?> getExpr() {
		return expr;
	}

	@Override
	public Expr<?> getExpression() {
		return expr;
	}

	@Override
	public XcfaLocation build(XcfaProcedure.Builder builder, XcfaLocation lastLoc, XcfaLocation breakLoc, XcfaLocation continueLoc, XcfaLocation returnLoc) {
		return lastLoc;
	}
}
