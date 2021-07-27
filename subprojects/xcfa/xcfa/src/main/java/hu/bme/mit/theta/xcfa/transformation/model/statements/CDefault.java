package hu.bme.mit.theta.xcfa.transformation.model.statements;

import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

public class CDefault extends CStatement{
	private final CStatement statement;

	public CDefault(CStatement statement) {
		this.statement = statement;
	}

	public CStatement getStatement() {
		return statement;
	}

	@Override
	public XcfaLocation build(XcfaProcedure.Builder builder, XcfaLocation lastLoc, XcfaLocation breakLoc, XcfaLocation continueLoc, XcfaLocation returnLoc) {
		return statement.build(builder, lastLoc, breakLoc, continueLoc, returnLoc);
	}
}
