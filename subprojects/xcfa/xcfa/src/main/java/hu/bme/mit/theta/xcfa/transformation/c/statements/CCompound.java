package hu.bme.mit.theta.xcfa.transformation.c.statements;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

public class CCompound extends CStatement{
	private final List<CStatement> cStatementList;

	public CCompound() {
		cStatementList = new ArrayList<>();
	}

	public List<CStatement> getcStatementList() {
		return cStatementList;
	}

	@Override
	public Expr<?> getExpression() {
		return cStatementList.get(cStatementList.size() - 1).getExpression();
	}

	@Override
	public XcfaLocation build(XcfaProcedure.Builder builder, XcfaLocation lastLoc, XcfaLocation breakLoc, XcfaLocation continueLoc, XcfaLocation returnLoc) {
		XcfaLocation initLoc = getLoc() == null ? new XcfaLocation("loc" + counter++, Map.of()) : getLoc();
		builder.addLoc(initLoc);
        propagateMetadata(initLoc);
		XcfaEdge edge = new XcfaEdge(lastLoc, initLoc, List.of());
		builder.addEdge(edge);
        propagateMetadata(edge);
		lastLoc = initLoc;
		for (CStatement statement : cStatementList) {
			if(statement != null) lastLoc = statement.build(builder, lastLoc, breakLoc, continueLoc, returnLoc);
		}
		return lastLoc;
	}
}
