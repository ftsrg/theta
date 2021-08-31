package hu.bme.mit.theta.xcfa.passes.procedurepass;

import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

public class RemoveDeadEnds extends ProcedurePass{
	@Override
	public XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {
		XcfaLocation errorLoc = builder.getErrorLoc();
		Set<XcfaEdge> nonDeadEndEdges = new LinkedHashSet<>();
		Set<XcfaEdge> reachableEdges = new LinkedHashSet<>();
		if(errorLoc != null) {
			collectNonDeadEndEdges(errorLoc, nonDeadEndEdges);
		}
		XcfaLocation finalLoc = builder.getFinalLoc();
		collectNonDeadEndEdges(finalLoc, nonDeadEndEdges);
		filterReachableEdges(builder.getInitLoc(), reachableEdges);
		Set<XcfaEdge> collect = builder.getEdges().stream().filter(xcfaEdge -> !nonDeadEndEdges.contains(xcfaEdge) || !reachableEdges.contains(xcfaEdge)).collect(Collectors.toSet());
		for (XcfaEdge edge : collect) {
			builder.removeEdge(edge);
		}
		List<XcfaLocation> toRemove = builder.getLocs().stream().filter(loc -> loc.getIncomingEdges().size() == 0 && loc.getOutgoingEdges().size() == 0 && !loc.isEndLoc() && !loc.isErrorLoc()).collect(Collectors.toList());
		for (XcfaLocation location : toRemove) {
			if(builder.getInitLoc() != location)
				builder.removeLoc(location);
		}
		return builder;
	}

	private void filterReachableEdges(XcfaLocation loc, Set<XcfaEdge> reachableEdges) {
		Set<XcfaLocation> waitlist = new LinkedHashSet<>();
		waitlist.add(loc);
		while (waitlist.size() > 0) {
			loc = waitlist.iterator().next();
			waitlist.remove(loc);
			List<XcfaEdge> outgoingEdges = loc.getOutgoingEdges();
			outgoingEdges.stream().filter(xcfaEdge -> !reachableEdges.contains(xcfaEdge)).map(XcfaEdge::getTarget).forEach(waitlist::add);
			reachableEdges.addAll(outgoingEdges);
		}

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
