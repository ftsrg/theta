/*
 * Copyright 2021 Budapest University of Technology and Economics
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package hu.bme.mit.theta.xcfa.model;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.SkipStmt;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.frontend.FrontendMetadata;
import hu.bme.mit.theta.xcfa.model.utils.XcfaLabelVarReplacer;
import hu.bme.mit.theta.xcfa.passes.XcfaPassManager;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.decl.Decls.Var;

/**
 * Represents an immutable Extended Control Flow Automata (XCFA). Use the builder class to
 * create a new instance.
 */
@SuppressWarnings("unused")
public final class XCFA {
	private final ImmutableMap<VarDecl<? extends Type>, Optional<LitExpr<?>>> globalVars;
	private final ImmutableList<XcfaProcess> processes;
	private final XcfaProcess mainProcess;
	private final String name;
	private final boolean dynamic;

	private XCFA(Builder builder) {
		globalVars = ImmutableMap.copyOf(builder.globalVars);
		processes = builder.processes.stream().map(builder1 -> builder1.build(this)).collect(ImmutableList.toImmutableList());
		mainProcess = builder.mainProcess.build(this);
		name = builder.name;
		dynamic = builder.dynamic;
	}

	public static Builder builder() {
		return new Builder();
	}

	/*
	 * Returns the equivalent CFA, if it exists.
	 */
	public CFA createCFA() {
		checkState(getProcesses().size() == 1, "XCFA cannot be converted to CFA because it has more than one process.");
		checkState(getMainProcess().getProcedures().size() == 1, "XCFA cannot be converted to CFA because it has more than one procedure.");

		CFA.Builder builder = CFA.builder();

		int tmpcnt = 0;

		Map<XcfaLocation, CFA.Loc> locationLUT = new LinkedHashMap<>();

		LinkedHashMap<VarDecl<?>, VarDecl<?>> varLut = new LinkedHashMap<>();
		int counter = 0;

		for (VarDecl<?> localVar : getMainProcess().getMainProcedure().getLocalVars()) {
			varLut.put(localVar, Var(localVar.getName() + "_id" + counter++, localVar.getType()));
		}

		for (XcfaLocation loc : getMainProcess().getMainProcedure().getLocs()) {
			CFA.Loc cfaLoc = builder.createLoc(loc.getName() + "_id" + counter++);
			FrontendMetadata.create(loc, "cfaLoc", cfaLoc);
			locationLUT.put(loc, cfaLoc);
		}

		for (XcfaEdge e : getMainProcess().getMainProcedure().getEdges()) {

			List<CFA.Loc> locations = new ArrayList<>();
			// Adding source
			locations.add(locationLUT.get(e.getSource()));
			// Adding intermediate locations (CFAs can only have one per edge)
			for (int i = 1; i < e.getLabels().size(); ++i) {
				CFA.Loc loc = builder.createLoc("tmp" + tmpcnt++);
				locations.add(loc);
				FrontendMetadata.create(e, "xcfaInterLoc", loc);
			}
			// Adding target
			locations.add(locationLUT.get(e.getTarget()));
			// Adding edges
			for (int i = 0; i < e.getLabels().size(); ++i) {
				CFA.Edge edge = builder.createEdge(locations.get(i), locations.get(i + 1), e.getLabels().get(i).accept(new XcfaLabelVarReplacer(), varLut).getStmt());
				FrontendMetadata.create(e, "cfaEdge", edge);
			}
			if (e.getLabels().size() == 0) {
				CFA.Edge edge = builder.createEdge(locations.get(0), locations.get(1), SkipStmt.getInstance());
				FrontendMetadata.create(e, "cfaEdge", edge);
			}
		}

		// Setting special locations (initial and final locations are mandatory, error location is not)
		builder.setInitLoc(locationLUT.get(getMainProcess().getMainProcedure().getInitLoc()));
		if (locationLUT.get(getMainProcess().getMainProcedure().getErrorLoc()) != null) builder.setErrorLoc(locationLUT.get(getMainProcess().getMainProcedure().getErrorLoc()));
		else builder.setErrorLoc(builder.createLoc());
		builder.setFinalLoc(locationLUT.get(getMainProcess().getMainProcedure().getFinalLoc()));

		return builder.build();
	}

	/*
	 * Getters
	 */

	public String getName() {
		return name;
	}

	public boolean isDynamic() {
		return dynamic;
	}

	/*
	 * Returns the XCFA as its graphviz representation
	 */
	public String toDot() {
		return toDot(List.of(), List.of());
	}
	public String toDot(Collection<String> cexLocations, Collection<XcfaEdge> cexEdges) {
		StringBuilder ret = new StringBuilder("digraph G{\n");
		for (VarDecl<? extends Type> globalVar : getGlobalVars()) {
			ret.append("\"var ").append(globalVar).append(" = ").append(getInitValue(globalVar).get()).append("\";\n");
		}
		ret.append(getMainProcess().toDot(cexLocations, cexEdges));
		ret.append("}\n");
		return ret.toString();
	}

	public List<VarDecl<? extends Type>> getGlobalVars() {
		return List.copyOf(globalVars.keySet());
	}

	public Optional<LitExpr<?>> getInitValue(final VarDecl<?> varDecl) {
		return globalVars.get(varDecl);
	}

	public List<XcfaProcess> getProcesses() {
		return processes;
	}

	public XcfaProcess getMainProcess() {
		return mainProcess;
	}

	public static final class Builder {
		private final Map<VarDecl<?>, Optional<LitExpr<?>>> globalVars;
		private final List<XcfaProcess.Builder> processes;
		private XcfaProcess.Builder mainProcess;
		private String name;
		private boolean dynamic;

		private XCFA built = null;

		private Builder() {
			globalVars = new LinkedHashMap<>();
			processes = new ArrayList<>();
		}

		private void checkNotBuilt() {
			checkState(built == null, "An XCFA was already built.");
		}

		// globalVars
		public Map<VarDecl<?>, Optional<LitExpr<?>>> getGlobalVars() {
			return globalVars;
		}

		public void addGlobalVar(final VarDecl<?> var, final LitExpr<?> initValue) {
			checkNotBuilt();
			globalVars.put(var, Optional.ofNullable(initValue));
		}

		// processes
		public List<XcfaProcess.Builder> getProcesses() {
			return processes;
		}

		public void addProcess(final XcfaProcess.Builder process) {
			checkNotBuilt();
			processes.add(process);
		}

		// mainProcess
		public XcfaProcess.Builder getMainProcess() {
			return mainProcess;
		}

		public void setMainProcess(final XcfaProcess.Builder mainProcess) {
			checkNotBuilt();
			checkArgument(processes.contains(mainProcess), "Invalid main process.");
			this.mainProcess = mainProcess;
		}

		//name
		public void setName(String name) {
			this.name = name;
		}

		//dynamic
		public void setDynamic(boolean dynamic) {
			this.dynamic = dynamic;
		}

		public XCFA build() {
			if(built != null) return built;

			checkState(mainProcess != null, "Main process must be set.");
			Builder builder = XcfaPassManager.run(this);
			XCFA xcfa = new XCFA(builder);
			built = xcfa;
			return xcfa;
		}

		public void runProcessPasses() {
			final ArrayList<XcfaProcess.Builder> newProcesses = new ArrayList<>();
			for (XcfaProcess.Builder process : processes) {
				final XcfaProcess.Builder newProc = XcfaPassManager.run(process);
				newProcesses.add(newProc);
				if(mainProcess == process) mainProcess = newProc;
			}
			this.processes.clear();
			this.processes.addAll(newProcesses);
		}
	}
}
