package hu.bme.mit.theta.xcfa.passes.procedurepass;

import hu.bme.mit.theta.frontend.FrontendMetadata;
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

public class RemoveDeadEnds extends ProcedurePass{

	// TODO: thread start and procedure call should not be dead-end! Use-case: while(1) pthread_create(..);
	@Override
	public XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {
		if(ArchitectureConfig.multiThreading) {
			Set<XcfaEdge> reachableEdges = new LinkedHashSet<>();
			filterReachableEdges(builder.getInitLoc(), reachableEdges);
			for (XcfaEdge edge : new ArrayList<>(builder.getEdges())) {
				if(!reachableEdges.contains(edge)) {
					builder.removeEdge(edge);
				}
			}
			return builder;
		} else {
			if(FrontendMetadata.lookupMetadata("shouldInline", false).size() > 0) return builder;
			Set<XcfaEdge> nonDeadEndEdges = new LinkedHashSet<>();
			Set<XcfaEdge> reachableEdges = new LinkedHashSet<>();
			XcfaLocation errorLoc = builder.getErrorLoc();

			Set<XcfaEdge> nonDeadEndFromErrorEdges = new LinkedHashSet<>();
			if (errorLoc != null) {
				collectNonDeadEndEdges(errorLoc, nonDeadEndFromErrorEdges);
			}

			Set<XcfaEdge> nonDeadEndFromFinalEdges = new LinkedHashSet<>();
			XcfaLocation finalLoc = builder.getFinalLoc();
			collectNonDeadEndEdges(finalLoc, nonDeadEndFromFinalEdges);

			nonDeadEndEdges.addAll(nonDeadEndFromErrorEdges);
			nonDeadEndEdges.addAll(nonDeadEndFromFinalEdges);

			filterReachableEdges(builder.getInitLoc(), reachableEdges);
			Set<XcfaEdge> collect = builder.getEdges().stream().filter(xcfaEdge -> !nonDeadEndEdges.contains(xcfaEdge)
					|| !reachableEdges.contains(xcfaEdge)).collect(Collectors.toSet());
			for (XcfaEdge edge : collect) {
				builder.removeEdge(edge);
			}
			List<XcfaLocation> toRemove = builder.getLocs().stream().filter(loc -> loc.getIncomingEdges().size() == 0
					&& loc.getOutgoingEdges().size() == 0 && !loc.isEndLoc()
					&& !loc.isErrorLoc()).collect(Collectors.toList());
			for (XcfaLocation location : toRemove) {
				if (builder.getInitLoc() != location)
					builder.removeLoc(location);
			}
			return builder;
		}
	}

	private void filterReachableEdges(XcfaLocation loc, Set<XcfaEdge> reachableEdges) {
		Set<XcfaEdge> outgoingEdges = new LinkedHashSet<>(loc.getOutgoingEdges());
		while(!outgoingEdges.isEmpty()) {
			Optional<XcfaEdge> any = outgoingEdges.stream().findAny();
			XcfaEdge outgoingEdge = any.get();
			outgoingEdges.remove(outgoingEdge);
			if (!reachableEdges.contains(outgoingEdge)) {
				reachableEdges.add(outgoingEdge);
				outgoingEdges.addAll(outgoingEdge.getTarget().getOutgoingEdges());
			}
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

	@Override
	public boolean isPostInlining() {
		return true;
	}
}
