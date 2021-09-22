package hu.bme.mit.theta.xcfa.passes.xcfapass;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.model.XcfaProcess;

import java.util.ArrayList;
import java.util.Map;
import java.util.Optional;

public class DemoteThreadLocalGlobals extends XcfaPass {
	@Override
	public XCFA.Builder run(XCFA.Builder builder) {
		for (Map.Entry<VarDecl<?>, Optional<LitExpr<?>>> entry : new ArrayList<>(builder.getGlobalVars().entrySet())) {
			VarDecl<?> varDecl = entry.getKey();
			Optional<LitExpr<?>> litExpr = entry.getValue();

			if(CComplexType.getType(varDecl.getRef()).isThreadLocal()) {
				builder.getGlobalVars().remove(varDecl);
				for (XcfaProcess.Builder process : builder.getProcesses()) {
					process.createVar(varDecl, litExpr.orElse(null));
				}
			}
		}
		return builder;
	}
}
