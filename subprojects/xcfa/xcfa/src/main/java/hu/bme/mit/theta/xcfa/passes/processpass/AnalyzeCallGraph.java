package hu.bme.mit.theta.xcfa.passes.processpass;

import hu.bme.mit.theta.frontend.FrontendMetadata;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.model.XcfaProcess;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

public class AnalyzeCallGraph extends ProcessPass {
	@Override
	public XcfaProcess.Builder run(XcfaProcess.Builder builder) {
		Map<XcfaProcedure.Builder, Set<XcfaProcedure.Builder>> calledBy = new LinkedHashMap<>();
		for (XcfaProcedure.Builder procedure : builder.getProcedures()) {
			calledBy.put(procedure, new LinkedHashSet<>());
		}

		for (XcfaProcedure.Builder procedure : builder.getProcedures()) {
			for (XcfaEdge edge : procedure.getEdges()) {
				for (XcfaLabel label : edge.getLabels()) {
					if(label instanceof XcfaLabel.ProcedureCallXcfaLabel) {
						XcfaLabel.ProcedureCallXcfaLabel callLabel = (XcfaLabel.ProcedureCallXcfaLabel) label;
						Optional<XcfaProcedure.Builder> procedureOpt = builder.getProcedures().stream().filter(xcfaProcedure -> xcfaProcedure.getName().equals(callLabel.getProcedure())).findAny();
						if(procedureOpt.isPresent()) {
							calledBy.get(procedureOpt.get()).add(procedure);
						} else {
							FrontendMetadata.create(callLabel.getProcedure(), "ownFunction", false);
						}
					}
				}
			}
		}

		boolean done = false;
		while(!done) {
			done = true;
			for (Map.Entry<XcfaProcedure.Builder, Set<XcfaProcedure.Builder>> entry : calledBy.entrySet()) {
				Set<XcfaProcedure.Builder> callers = entry.getValue();
				for (XcfaProcedure.Builder caller : new LinkedHashSet<>(callers)) {
					Set<XcfaProcedure.Builder> newCallers = calledBy.get(caller);
					if(!callers.containsAll(newCallers)) {
						done = false;
					}
					callers.addAll(newCallers);
				}
			}
		}

		FrontendMetadata.lookupMetadata("shouldInline", false).stream().filter(o -> o instanceof String).collect(Collectors.toList()).forEach(o -> {
			final Optional<XcfaProcedure.Builder> any = builder.getProcedures().stream().filter(builder1 -> builder1.getName().equals(o)).findAny();
			FrontendMetadata.create(any.get(), "shouldKeep", true);
		});

		calledBy.forEach((procedure, xcfaProcedures) -> {
			if(xcfaProcedures.contains(procedure)) {
				FrontendMetadata.create(procedure, "shouldInline", false);
			}
		});

		return builder;
	}
}
