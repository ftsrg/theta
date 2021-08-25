package hu.bme.mit.theta.xcfa.passes.procedurepass;

import com.google.common.collect.Streams;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import java.util.stream.Collectors;

import static hu.bme.mit.theta.xcfa.passes.procedurepass.Utils.collectReverseEdges;

public class UnrollLoopsPass extends ProcedurePass{

	private final Set<XcfaEdge> forwardEdges = new LinkedHashSet<>();
	private final Set<XcfaLocation> originalLocs = new LinkedHashSet<>();
	private final Set<XcfaEdge> reverseEdges = new LinkedHashSet<>();
	private final Map<XcfaLocation, Stack<XcfaLocation>> locationCopies = new LinkedHashMap<>();

	@Override
	public XcfaProcedure.Builder run(XcfaProcedure.Builder input) {
		XcfaProcedure.Builder builder = EliminateSelfLoops.instance.run(input);
		if(originalLocs.isEmpty()) {
			Set<XcfaEdge> reverseEdges = collectReverseEdges(builder.getInitLoc());
			Set<XcfaLocation> toDuplicate = new LinkedHashSet<>();
			reverseEdges.stream().filter(xcfaEdge -> reverseEdges.stream().anyMatch(xcfaEdge1 -> xcfaEdge.getTarget() == xcfaEdge1.getSource())).forEach(xcfaEdge -> toDuplicate.add(xcfaEdge.getTarget()));
			if(!toDuplicate.isEmpty()) {
				for (XcfaLocation location : toDuplicate) {
					XcfaLocation copy = XcfaLocation.copyOf(location);
					builder.addLoc(copy);
					for (XcfaEdge incomingEdge : new LinkedHashSet<>(location.getIncomingEdges())) {
						builder.removeEdge(incomingEdge);
						builder.addEdge(new XcfaEdge(incomingEdge.getSource(), copy, incomingEdge.getStmts()));
					}
					builder.addEdge(new XcfaEdge(copy, location, List.of()));
				}
				this.reverseEdges.addAll(collectReverseEdges(builder.getInitLoc()));
			} else {
				this.reverseEdges.addAll(reverseEdges);
			}
			forwardEdges.addAll(builder.getEdges().stream().filter(xcfaEdge -> !this.reverseEdges.contains(xcfaEdge)).collect(Collectors.toSet()));
			originalLocs.addAll(builder.getLocs());
			for (XcfaLocation location : builder.getLocs()) {
				locationCopies.putIfAbsent(location, new Stack<>());
				locationCopies.get(location).push(location);
			}
		}

		Map<XcfaLocation, XcfaLocation> locationLut = new LinkedHashMap<>();
		Map<XcfaLocation, XcfaLocation> lastLocationLut = new LinkedHashMap<>();
		originalLocs.forEach(location -> {
			XcfaLocation copy = XcfaLocation.copyOf(location);
			locationLut.put(location, copy);
			lastLocationLut.put(location, locationCopies.get(location).peek());
			locationCopies.get(location).push(copy);
			builder.addLoc(copy);
		});

		//noinspection UnstableApiUsage
		Streams.concat(forwardEdges.stream(), reverseEdges.stream()).forEach(xcfaEdge -> builder.addEdge(new XcfaEdge(locationLut.get(xcfaEdge.getSource()), locationLut.get(xcfaEdge.getTarget()), xcfaEdge.getStmts())));

		for (XcfaEdge reverseEdge : reverseEdges) {
			XcfaLocation source = lastLocationLut.get(reverseEdge.getSource());
			XcfaLocation target = locationLut.get(reverseEdge.getTarget());
			builder.addEdge(new XcfaEdge(source, target, reverseEdge.getStmts()));

			for (XcfaEdge outgoingEdge : reverseEdge.getSource().getOutgoingEdges()) {
				source = locationLut.get(reverseEdge.getSource());
				if(forwardEdges.contains(outgoingEdge)) {
					for (XcfaLocation forwardTarget : locationCopies.get(reverseEdge.getSource())) {
						if(source != forwardTarget)
							builder.addEdge(new XcfaEdge(source, forwardTarget, outgoingEdge.getStmts()));
					}
				}
			}
		}

		return builder;
	}
}
