package hu.bme.mit.theta.frontend.transformation.model.statements;

import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

public class CCase extends CStatement{
	private final CStatement expr;
	private final CStatement statement;

	public CCase(CStatement expr, CStatement statement) {
		this.expr = expr;
		this.statement = statement;
	}

	public CStatement getExpr() {
		return expr;
	}

	public CStatement getStatement() {
		return statement;
	}

	@Override
	public XcfaLocation build(XcfaProcedure.Builder builder, XcfaLocation lastLoc, XcfaLocation breakLoc, XcfaLocation continueLoc, XcfaLocation returnLoc) {
		return statement.build(builder, lastLoc, breakLoc, continueLoc, returnLoc);
	}
}
