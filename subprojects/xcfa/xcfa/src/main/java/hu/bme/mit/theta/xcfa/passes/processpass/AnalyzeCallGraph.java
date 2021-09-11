package hu.bme.mit.theta.xcfa.passes.processpass;

import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.stmt.xcfa.XcfaCallStmt;
import hu.bme.mit.theta.frontend.FrontendMetadata;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.model.XcfaProcess;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

public class AnalyzeCallGraph extends ProcessPass {
	@Override
	public XcfaProcess.Builder run(XcfaProcess.Builder builder) {
		Map<XcfaProcedure, Set<XcfaProcedure>> calledBy = new LinkedHashMap<>();
		for (XcfaProcedure procedure : builder.getProcedures()) {
			calledBy.put(procedure, new LinkedHashSet<>());
		}

		for (XcfaProcedure procedure : builder.getProcedures()) {
			for (XcfaEdge edge : procedure.getEdges()) {
				for (Stmt stmt : edge.getLabels()) {
					if(stmt instanceof XcfaCallStmt) {
						XcfaCallStmt callStmt = (XcfaCallStmt) stmt;
						Optional<XcfaProcedure> procedureOpt = builder.getProcedures().stream().filter(xcfaProcedure -> xcfaProcedure.getName().equals(callStmt.getProcedure())).findAny();
						if(procedureOpt.isPresent()) {
							calledBy.get(procedureOpt.get()).add(procedure);
						} else {
							FrontendMetadata.create(((XcfaCallStmt) stmt).getProcedure(), "ownFunction", false);
						}
					}
				}
			}
		}

		boolean done = false;
		while(!done) {
			done = true;
			for (Map.Entry<XcfaProcedure, Set<XcfaProcedure>> entry : calledBy.entrySet()) {
				XcfaProcedure callee = entry.getKey();
				Set<XcfaProcedure> callers = entry.getValue();
				for (XcfaProcedure caller : new LinkedHashSet<>(callers)) {
					Set<XcfaProcedure> newCallers = calledBy.get(caller);
					if(!callers.containsAll(newCallers)) {
						done = false;
					}
					callers.addAll(newCallers);
				}
			}
		}

		calledBy.forEach((procedure, xcfaProcedures) -> {
			if(xcfaProcedures.contains(procedure)) {
				FrontendMetadata.create(procedure, "shouldInline", false);
			}
		});
		return builder;
	}
}
