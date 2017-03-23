package hu.bme.mit.theta.formalism.xta;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.collect.ImmutableList.toImmutableList;

import java.util.Collection;
import java.util.HashSet;
import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.formalism.ta.decl.ClockDecl;

public final class XtaSystem {
	private final Collection<VarDecl<?>> vars;
	private final Collection<ClockDecl> clocks;
	private final List<XtaProcess> processes;

	private XtaSystem(final List<XtaProcess> processes) {
		checkNotNull(processes);
		checkArgument(processes.size() > 0);
		this.processes = ImmutableList.copyOf(processes);
		vars = new HashSet<>();
		processes.forEach(p -> vars.addAll(p.getVars()));
		clocks = vars.stream().filter(v -> v instanceof ClockDecl).map(v -> (ClockDecl) v).collect(toImmutableList());
	}

	public static XtaSystem of(final List<XtaProcess> processes) {
		return new XtaSystem(processes);
	}

	public Collection<VarDecl<?>> getVars() {
		return vars;
	}

	public Collection<ClockDecl> getClocks() {
		return clocks;
	}

	public List<XtaProcess> getProcesses() {
		return processes;
	}

}
