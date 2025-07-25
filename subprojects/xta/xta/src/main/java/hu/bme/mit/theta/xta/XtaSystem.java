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

import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.rattype.RatType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.xta.XtaProcess.Loc;

import java.lang.management.LockInfo;
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


	private Expr<BoolType> prop;
	private PropertyKind propertyKind = PropertyKind.NONE;

	private XtaSystem() {
		processes = new ArrayList<>();
		dataVars = Containers.createSet();
		clockVars = Containers.createSet();
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

	public Expr<BoolType> getProp(){
		return prop;
	}

	public PropertyKind getPropertyKind() {
		return propertyKind;
	}

	public void setProp(final Expr<BoolType> _prop, final PropertyKind _propertyKind){

		prop = _prop;
		propertyKind = _propertyKind;
		//ErrorProcess
		XtaProcess process = createProcess("ErrorProc");
		final Collection<Expr<BoolType>> invars = Collections.emptySet();
		Loc initloc = process.createLoc("InitLoc", XtaProcess.LocKind.NORMAL, invars);
		process.setInitLoc(initloc);
		Loc errorLoc = process.createLoc("ErrorLoc", XtaProcess.LocKind.ERROR, invars);
		final Collection<Expr<BoolType>> guards = ExprUtils.getConjuncts(ExprUtils.simplify(prop));
		process.createEdge(initloc, errorLoc, Collections.emptyList(), guards, Optional.empty(), Collections.emptyList());

		//Edges to ErrorLocations from COMMITTED locations

		for (XtaProcess proc: processes) {
			if (!proc.getName().equals("ErrorProc")) {
				Loc own_errorLoc = proc.createLoc("ErrorLoc", XtaProcess.LocKind.ERROR, invars);
				for (Loc loc:proc.getLocs() ) {
					if(loc.getKind().equals(XtaProcess.LocKind.COMMITTED))
						proc.createEdge(loc, own_errorLoc, Collections.emptyList(), guards, Optional.empty(),Collections.emptyList());
				}
			}

		}
	}

	public enum PropertyKind {
		AG, AF, EG, EF, NONE
	}
}
