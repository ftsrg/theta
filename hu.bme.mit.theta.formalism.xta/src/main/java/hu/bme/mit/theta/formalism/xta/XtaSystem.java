/*
 *  Copyright 2017 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.formalism.xta;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.collect.ImmutableList.toImmutableList;
import static com.google.common.collect.ImmutableSet.toImmutableSet;

import java.util.Collection;
import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.rattype.RatType;
import hu.bme.mit.theta.formalism.xta.XtaProcess.Loc;

public final class XtaSystem {
	private final List<XtaProcess> processes;
	private final Collection<VarDecl<?>> dataVars;
	private final Collection<VarDecl<RatType>> clockVars;
	private final List<Loc> initLocs;

	private XtaSystem(final List<XtaProcess> processes) {
		checkNotNull(processes);
		checkArgument(!processes.isEmpty());
		this.processes = ImmutableList.copyOf(processes);
		dataVars = processes.stream().flatMap(p -> p.getDataVars().stream()).collect(toImmutableSet());
		clockVars = processes.stream().flatMap(p -> p.getClockVars().stream()).collect(toImmutableSet());
		initLocs = processes.stream().map(XtaProcess::getInitLoc).collect(toImmutableList());
	}

	public static XtaSystem of(final List<XtaProcess> processes) {
		return new XtaSystem(processes);
	}

	public List<XtaProcess> getProcesses() {
		return processes;
	}

	public Collection<VarDecl<?>> getDataVars() {
		return dataVars;
	}

	public Collection<VarDecl<RatType>> getClockVars() {
		return clockVars;
	}

	public List<Loc> getInitLocs() {
		return initLocs;
	}

}
