package hu.bme.mit.theta.xcfa.transformation.c.statements;

import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

import java.util.List;
import java.util.Map;

public class CContinue extends CStatement{

	@Override
	public XcfaLocation build(XcfaProcedure.Builder builder, XcfaLocation lastLoc, XcfaLocation breakLoc, XcfaLocation continueLoc, XcfaLocation returnLoc) {
		XcfaLocation initLoc = getLoc() == null ? new XcfaLocation("loc" + counter++, Map.of()) : getLoc();
		builder.addLoc(initLoc);
		XcfaEdge edge = new XcfaEdge(lastLoc, initLoc, List.of());
		builder.addEdge(edge);
		edge = new XcfaEdge(initLoc, continueLoc, List.of());
		XcfaLocation unreachableLoc = new XcfaLocation("Unreachable", Map.of());
		builder.addLoc(unreachableLoc);
		builder.addEdge(edge);
		return unreachableLoc;
	}
}
