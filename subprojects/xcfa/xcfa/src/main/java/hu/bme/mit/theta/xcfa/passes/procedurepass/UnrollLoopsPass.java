package hu.bme.mit.theta.xcfa.passes.procedurepass;

import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static com.google.common.base.Preconditions.checkNotNull;

public class UnrollLoopsPass extends ProcedurePass{
	private static final int K = 1;

	@Override
	public XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {
		XcfaProcedure.Builder newBuilder = XcfaProcedure.builder();
		Set<XcfaLocation> visitedLocations = new LinkedHashSet<>();
		Map<XcfaEdge, Integer> visitedReverseEdges = new LinkedHashMap<>();
		XcfaLocation head = builder.getInitLoc();
		inline(newBuilder, head, getCopy(newBuilder, head), visitedLocations, visitedReverseEdges);
		newBuilder.setInitLoc(getOriginal(head));
		newBuilder.setFinalLoc(getOriginal(builder.getFinalLoc()));
		return newBuilder;
	}

	private void inline(XcfaProcedure.Builder newBuilder, XcfaLocation head, XcfaLocation copyHead, Set<XcfaLocation> visitedLocations, Map<XcfaEdge, Integer> visitedReverseEdges) {
		newBuilder.addLoc(copyHead);
		visitedLocations.add(head);
		List<XcfaEdge> outgoingEdges = head.getOutgoingEdges();
		for (XcfaEdge outgoingEdge : outgoingEdges) {
			if(visitedLocations.contains(outgoingEdge.getTarget())) {
				Integer visited = visitedReverseEdges.getOrDefault(outgoingEdge, 0);
				if(visited < K) {
					visitedReverseEdges.put(outgoingEdge, visited+1);
					XcfaLocation newTarget = getCopy(newBuilder, outgoingEdge.getTarget());
					newBuilder.addEdge(new XcfaEdge(copyHead, newTarget, outgoingEdge.getStmts()));
					inline(newBuilder, outgoingEdge.getTarget(), newTarget, visitedLocations, visitedReverseEdges);
				} else {
					XcfaLocation oldTarget = getOriginal(outgoingEdge.getTarget());
					newBuilder.addEdge(new XcfaEdge(copyHead, oldTarget, outgoingEdge.getStmts()));
				}
			}
			else {;
				XcfaLocation newTarget = getCopy(newBuilder, outgoingEdge.getTarget());
				newBuilder.addEdge(new XcfaEdge(copyHead, newTarget, outgoingEdge.getStmts()));
				inline(newBuilder, outgoingEdge.getTarget(), newTarget, visitedLocations, visitedReverseEdges);
			}
		}
	}

	private final Map<XcfaLocation, XcfaLocation> originalLocationLut = new LinkedHashMap<>();
	private XcfaLocation getCopy(XcfaProcedure.Builder newBuilder, XcfaLocation loc) {
		XcfaLocation newLoc = XcfaLocation.copyOf(loc);
		originalLocationLut.putIfAbsent(loc, newLoc);
		newBuilder.addLoc(newLoc);
		return newLoc;
	}
	private XcfaLocation getOriginal(XcfaLocation loc) {
		return checkNotNull(originalLocationLut.get(loc));
	}
}
