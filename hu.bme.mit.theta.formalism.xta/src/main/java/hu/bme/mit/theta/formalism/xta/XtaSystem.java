package hu.bme.mit.theta.formalism.xta;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.collect.ImmutableSet.toImmutableSet;

import java.util.Collection;
import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.rattype.RatType;

public final class XtaSystem {
	private final Collection<VarDecl<?>> dataVars;
	private final Collection<VarDecl<RatType>> clockVars;
	private final List<XtaProcess> processes;

	private XtaSystem(final List<XtaProcess> processes) {
		checkNotNull(processes);
		checkArgument(processes.size() > 0);
		this.processes = ImmutableList.copyOf(processes);
		dataVars = processes.stream().flatMap(p -> p.getDataVars().stream()).collect(toImmutableSet());
		clockVars = processes.stream().flatMap(p -> p.getClockVars().stream()).collect(toImmutableSet());
	}

	public static XtaSystem of(final List<XtaProcess> processes) {
		return new XtaSystem(processes);
	}

	public Collection<VarDecl<?>> getDataVars() {
		return dataVars;
	}

	public Collection<VarDecl<RatType>> getClockVars() {
		return clockVars;
	}

	public List<XtaProcess> getProcesses() {
		return processes;
	}

}
