package hu.bme.mit.theta.formalism.xta;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.HashSet;
import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.core.decl.VarDecl;

public final class XtaSystem {
	private final Collection<VarDecl<?>> vars;
	private final List<XtaProcess> processes;

	private XtaSystem(final List<XtaProcess> processes) {
		checkNotNull(processes);
		checkArgument(processes.size() > 0);
		this.processes = ImmutableList.copyOf(processes);
		vars = new HashSet<>();
		processes.forEach(p -> vars.addAll(p.getVars()));
	}

	public static XtaSystem of(final List<XtaProcess> processes) {
		return new XtaSystem(processes);
	}

	public Collection<VarDecl<?>> getVars() {
		return vars;
	}

	public List<XtaProcess> getProcesses() {
		return processes;
	}

}
