package hu.bme.mit.theta.xcfa.transformation.model.statements;

import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

import java.util.List;
import java.util.Map;

public class CGoto extends CStatement{
	private final String id;

	public CGoto(String id) {
		this.id = id;
	}

	public String getId() {
		return id;
	}

	@Override
	public XcfaLocation build(XcfaProcedure.Builder builder, XcfaLocation lastLoc, XcfaLocation breakLoc, XcfaLocation continueLoc, XcfaLocation returnLoc) {
		XcfaLocation initLoc = getLoc() == null ? new XcfaLocation("loc" + counter++, Map.of()) : getLoc();
		builder.addLoc(initLoc);
        propagateMetadata(initLoc);
		XcfaEdge edge = new XcfaEdge(lastLoc, initLoc, List.of());
		builder.addEdge(edge);
        propagateMetadata(edge);
		edge = new XcfaEdge(initLoc, CFunction.globalLocLut.get(id), List.of());
		builder.addLoc(CFunction.globalLocLut.get(id));
		XcfaLocation unreachableLoc = new XcfaLocation("Unreachable", Map.of());
		builder.addLoc(unreachableLoc);
        propagateMetadata(unreachableLoc);
		builder.addEdge(edge);
        propagateMetadata(edge);
		return unreachableLoc;
	}
}
