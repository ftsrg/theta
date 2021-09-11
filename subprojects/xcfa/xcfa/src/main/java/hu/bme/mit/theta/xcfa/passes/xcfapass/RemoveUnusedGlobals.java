package hu.bme.mit.theta.xcfa.passes.xcfapass;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.model.XcfaProcess;

import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import static hu.bme.mit.theta.xcfa.passes.procedurepass.Utils.getVars;

public class RemoveUnusedGlobals extends XcfaPass {
	@Override
	public XCFA.Builder run(XCFA.Builder builder) {
		Set<VarDecl<?>> usedGlobals = new LinkedHashSet<>();
		for (XcfaProcess.Builder process : builder.getProcesses()) {
			for (XcfaProcedure.Builder procedure : process.getProcedures()) {
				for (XcfaEdge edge : procedure.getEdges()) {
					for (XcfaLabel label : edge.getLabels()) {
						usedGlobals.addAll(getVars(label));
					}
				}
			}
		}
		Set<Map.Entry<VarDecl<?>, Optional<LitExpr<?>>>> newGlobals = builder.getGlobalVars().entrySet().stream().filter(varDeclOptionalEntry -> usedGlobals.contains(varDeclOptionalEntry.getKey())).collect(Collectors.toSet());
		builder.getGlobalVars().clear();
		for (Map.Entry<VarDecl<?>, Optional<LitExpr<?>>> newGlobal : newGlobals) {
			builder.addGlobalVar(newGlobal.getKey(), newGlobal.getValue().orElse(null));
		}
		return builder;
	}
}
