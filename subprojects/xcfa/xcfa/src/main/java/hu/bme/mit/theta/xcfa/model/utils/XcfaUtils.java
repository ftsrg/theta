package hu.bme.mit.theta.xcfa.model.utils;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.xcfa.model.XCFA;

import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.Set;

public class XcfaUtils {

	public static Collection<VarDecl<?>> getVars(XCFA xcfa) {
		Set<VarDecl<?>> ret = new LinkedHashSet<>(xcfa.getGlobalVars());
		xcfa.getProcesses().forEach(process -> {
			ret.addAll(process.getParams());
			ret.addAll(process.getThreadLocalVars());
			process.getProcedures().forEach(procedure -> {
				ret.addAll(procedure.getParams().keySet());
				ret.addAll(procedure.getLocalVars());
			});
		});
		return ret;
	}
}
