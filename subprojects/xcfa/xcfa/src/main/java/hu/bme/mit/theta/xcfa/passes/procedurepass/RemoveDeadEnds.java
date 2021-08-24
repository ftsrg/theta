package hu.bme.mit.theta.xcfa.passes.procedurepass;

import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

import java.util.LinkedHashSet;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

public class RemoveDeadEnds extends ProcedurePass{
	@Override
	public XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {
		XcfaLocation errorLoc = builder.getErrorLoc();
		Set<XcfaEdge> nonDeadEndEdges = new LinkedHashSet<>();
		if(errorLoc != null) {
			collectNonDeadEndEdges(errorLoc, nonDeadEndEdges);
		}
		XcfaLocation finalLoc = builder.getFinalLoc();
		collectNonDeadEndEdges(finalLoc, nonDeadEndEdges);
		Set<XcfaEdge> collect = builder.getEdges().stream().filter(xcfaEdge -> !nonDeadEndEdges.contains(xcfaEdge)).collect(Collectors.toSet());
		for (XcfaEdge edge : collect) {
			builder.removeEdge(edge);
		}
		builder.getLocs().removeIf(loc -> loc.getIncomingEdges().size() == 0 && loc.getOutgoingEdges().size() == 0);
		return builder;
	}

	private void collectNonDeadEndEdges(XcfaLocation loc, Set<XcfaEdge> nonDeadEndEdges) {
		Set<XcfaEdge> incomingEdges = new LinkedHashSet<>(loc.getIncomingEdges());
		while(!incomingEdges.isEmpty()) {
			Optional<XcfaEdge> any = incomingEdges.stream().findAny();
			XcfaEdge incomingEdge = any.get();
			incomingEdges.remove(incomingEdge);
			if (!nonDeadEndEdges.contains(incomingEdge)) {
				nonDeadEndEdges.add(incomingEdge);
				incomingEdges.addAll(incomingEdge.getSource().getIncomingEdges());
			}
		}
	}
}
