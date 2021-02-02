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
package hu.bme.mit.theta.xta;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.rattype.RatType;
import hu.bme.mit.theta.xta.XtaProcess.Loc;

import java.util.*;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.collect.ImmutableList.toImmutableList;

public final class XtaSystem {
	private final List<XtaProcess> processes;
	private final Collection<VarDecl<?>> dataVars;
	private final Collection<VarDecl<RatType>> clockVars;
	private final MutableValuation initVal;

	private final List<XtaProcess> unmodProcesses;
	private final Collection<VarDecl<?>> unmodDataVars;
	private final Collection<VarDecl<RatType>> unmodClockVars;

	private XtaSystem() {
		processes = new ArrayList<>();
		dataVars = new HashSet<>();
		clockVars = new HashSet<>();
		initVal = new MutableValuation();

		unmodProcesses = Collections.unmodifiableList(processes);
		unmodDataVars = Collections.unmodifiableCollection(dataVars);
		unmodClockVars = Collections.unmodifiableCollection(clockVars);
	}

	public static XtaSystem create() {
		return new XtaSystem();
	}

	public List<XtaProcess> getProcesses() {
		return unmodProcesses;
	}

	public Collection<VarDecl<?>> getDataVars() {
		return unmodDataVars;
	}

	public Collection<VarDecl<RatType>> getClockVars() {
		return unmodClockVars;
	}

	// TODO Return value is not immutable
	public Valuation getInitVal() {
		return initVal;
	}

	public List<Loc> getInitLocs() {
		return processes.stream().map(XtaProcess::getInitLoc).collect(toImmutableList());
	}

	////

	public void addDataVar(final VarDecl<?> varDecl, final LitExpr<?> initValue) {
		checkNotNull(varDecl);
		checkNotNull(initValue);
		checkArgument(!clockVars.contains(varDecl));
		dataVars.add(varDecl);
		initVal.put(varDecl, initValue);
	}

	public void addClockVar(final VarDecl<RatType> varDecl) {
		checkNotNull(varDecl);
		checkArgument(!dataVars.contains(varDecl));
		clockVars.add(varDecl);
	}

	public XtaProcess createProcess(final String name) {
		final XtaProcess process = XtaProcess.create(this, name);
		processes.add(process);
		return process;
	}
}
