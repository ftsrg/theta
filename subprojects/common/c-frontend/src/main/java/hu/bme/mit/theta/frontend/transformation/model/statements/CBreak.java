package hu.bme.mit.theta.frontend.transformation.model.statements;

import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

import java.util.List;
import java.util.Map;

public class CBreak extends CStatement{

	@Override
	public XcfaLocation build(XcfaProcedure.Builder builder, XcfaLocation lastLoc, XcfaLocation breakLoc, XcfaLocation continueLoc, XcfaLocation returnLoc) {
		XcfaLocation initLoc = getLoc() == null ? new XcfaLocation("loc" + counter++, Map.of()) : getLoc();
		builder.addLoc(initLoc);
        propagateMetadata(initLoc);
		XcfaEdge edge = new XcfaEdge(lastLoc, initLoc, List.of());
		builder.addEdge(edge);
        propagateMetadata(edge);
		edge = new XcfaEdge(initLoc, breakLoc, List.of());
		XcfaLocation unreachableLoc = new XcfaLocation("Unreachable", Map.of());
		builder.addLoc(unreachableLoc);
        propagateMetadata(unreachableLoc);
		builder.addEdge(edge);
        propagateMetadata(edge);
		return unreachableLoc;
	}
}
