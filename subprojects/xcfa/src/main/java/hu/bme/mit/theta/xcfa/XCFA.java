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
package hu.bme.mit.theta.xcfa;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.Tuple3;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.XcfaStmt;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.xcfa.dsl.XcfaDslManager;
import hu.bme.mit.theta.xcfa.ir.InstructionHandler;
import hu.bme.mit.theta.xcfa.ir.LlvmIrProvider;
import hu.bme.mit.theta.xcfa.ir.SSAProvider;

import java.io.*;
import java.util.*;

import static com.google.common.base.Preconditions.*;
import static hu.bme.mit.theta.xcfa.ir.Utils.*;

/**
 * Represents an Extended Control Flow Automata (XCFA). Use the builder class to
 * create a new instance.
 */
@SuppressWarnings("unused")
public final class XCFA {

	/*
	 * Creates an XCFA from the provided InputStream using the XCFA DSL.
	 */
	public static XCFA createXCFA(InputStream dsl) throws IOException {
		return XcfaDslManager.createXcfa(dsl);
	}

	/*
	 * Creates an XCFA from the provided String using the XCFA DSL
	 */
	public static XCFA createXCFA(String dsl) throws IOException {
		return XcfaDslManager.createXcfa(dsl);
	}

	/*
	 * Creates an XCFA from the provided SSAProvider using its getter methods.
	 */
	public static XCFA createXCFA(SSAProvider ssa) {
		Map<String, VarDecl<?>> globalVarLut = new HashMap<>();
		XCFA.Builder builder = new XCFA.Builder();

		// Creating global variables
		for (Tuple3<String, String, String> globalVariable : ssa.getGlobalVariables()) {

			VarDecl<?> variable = createVariable(globalVariable.get1(), globalVariable.get2());
			globalVarLut.put(globalVariable.get1(), variable);
			builder.globalVars.put(variable, createConstant(globalVariable.get3()));

		}

		Map<String, XCFAProcedure> procedures = new LinkedHashMap<>();
		Map<XCFAProcess.Builder, String> processBuilders = new HashMap<>();
		List<InstructionHandler> instructionHandlers = new ArrayList<>();

		XCFAProcess.Builder mainProcBuilder = XCFAProcess.builder();
		mainProcBuilder.setName("main");
		processBuilders.put(mainProcBuilder, mainProcBuilder.getName());

		// Creating procedures
		for (Tuple3<String, Optional<String>, List<Tuple2<String, String>>> function : ssa.getFunctions()) {

			XCFAProcedure.Builder procedureBuilder = XCFAProcedure.builder();
			procedureBuilder.setName(function.get1());

			Collection<String> processes = new ArrayList<>();

			instructionHandlers.add(handleProcedure(function, procedureBuilder, ssa, globalVarLut, processes));

			for (String process : processes) {

				XCFAProcess.Builder processBuilder = XCFAProcess.builder();
				processBuilder.setName(process);
				processBuilders.put(processBuilder, function.get1());

			}

			XCFAProcedure procedure = procedureBuilder.build();
			procedures.put(function.get1(), procedure);
		}

		// Letting procedures finish setting up their call statements (by providing them with a list of built procedures)
		for (InstructionHandler instructionHandler : instructionHandlers) {
			instructionHandler.substituteProcedures(procedures);
		}

		// Instantiating procedures, each with a copy of each procedure.
		for (Map.Entry<XCFAProcess.Builder, String> entry : processBuilders.entrySet()) {
			XCFAProcess.Builder processBuilder = entry.getKey();
			String mainProcedureName = entry.getValue();

			for (Map.Entry<String, XCFAProcedure> e : procedures.entrySet()) {
				String procedureName = e.getKey();
				XCFAProcedure procedure = e.getValue();

				XCFAProcedure proc = new XCFAProcedure(procedure);
				processBuilder.addProcedure(proc);
				if (procedureName.equals(mainProcedureName)) processBuilder.setMainProcedure(proc);

			}

			XCFAProcess proc = processBuilder.build();
			builder.addProcess(proc);

			if (processBuilder == mainProcBuilder) builder.setMainProcess(proc);

		}

		return builder.build();
	}

	/*
	 * Creates an XCFA from the specified file.
	 * This is the recommended method for getting an XCFA instance.
	 * Supports .xcfa, .ll, .bc, .c and .i files.
	 */
    public static XCFA fromFile(File model) throws IOException {

		if(!model.exists()) throw new FileNotFoundException();

		if(model.getName().endsWith(".xcfa")) {
			try(InputStream is = new FileInputStream(model)) {
				return createXCFA(is);
			}

		}else if ( model.getName().endsWith(".ll") || model.getName().endsWith(".bc") ){
			return createXCFA(new LlvmIrProvider(model.getAbsolutePath()));

		} else if ( model.getName().endsWith(".c") || model.getName().endsWith(".i") ) {
			throw new RuntimeException(".c or .i files are not yet supported.");

		} else {
			String[] split = model.getName().split("\\.");
			if(split.length > 0)
				throw new RuntimeException("File type " + split[split.length-1] + " not supported.");
			throw new RuntimeException("File does not have an extension.");

		}
    }

	/*
	 * Returns a new XCFA.Builder instance
	 */
	public static Builder builder() {
		return new Builder();
	}

	private final Map<VarDecl<? extends Type>, LitExpr<?>> globalVars;

	private final List<XCFAProcess> processes;
	private final XCFAProcess mainProcess;

	private XCFA(Builder builder) {
		globalVars = builder.globalVars;
		processes = ImmutableList.copyOf(builder.processes);
		processes.forEach(process -> process.setParent(this));
		mainProcess = builder.mainProcess;
	}

	/*
	 * Returns the equivalent CFA, if it exists.
	 */
	public CFA createCFA() {
		checkState(getProcesses().size() == 1, "XCFA cannot be converted to CFA because it has more than one process.");
		checkState(getMainProcess().getProcedures().size() == 1, "XCFA cannot be converted to CFA because it has more than one procedure.");

		CFA.Builder builder = CFA.builder();
		CFA.Loc initLoc = null;
		CFA.Loc errorLoc = null;
		CFA.Loc finalLoc = null;

		int tmpcnt = 0;

		for (XCFAProcedure.Edge e : getMainProcess().getMainProcedure().getEdges()) {

			List<CFA.Loc> locations = new ArrayList<>();
			// Adding source
			locations.add(builder.createLoc(e.getSource().getName()));
			// Adding intermediate locations (CFAs can only have one per edge)
			for (int i = 1; i < e.getStmts().size(); ++i) {
				locations.add(builder.createLoc("tmp" + tmpcnt++));
			}
			// Adding target
			locations.add(builder.createLoc(e.getTarget().getName()));
			// Adding edges
			for (int i = 0; i < e.getStmts().size(); ++i) {
				checkState( ! (e.getStmts().get(i) instanceof XcfaStmt), "XCFA statement " + e.getStmts().get(i) + " is not supported!");
				builder.createEdge(locations.get(i), locations.get(i + 1), e.getStmts().get(i));
			}
			// Deciding if the source or target is any special location
			if (e.getSource() == getMainProcess().getMainProcedure().getInitLoc()) initLoc = locations.get(0);
			if (e.getTarget() == getMainProcess().getMainProcedure().getErrorLoc()) errorLoc = locations.get(locations.size() - 1);
			else if (e.getTarget() == getMainProcess().getMainProcedure().getFinalLoc()) finalLoc = locations.get(locations.size() - 1);
		}
		// Setting special locations (initial and final locations are mandatory, error location is not)
		builder.setInitLoc(initLoc);
		if(errorLoc != null) builder.setErrorLoc(errorLoc);
		builder.setFinalLoc(finalLoc);

		return builder.build();
	}

	/*
	 * Returns the XCFA as its graphviz representation
	 */
	public String toDot() {
		StringBuilder ret = new StringBuilder("digraph G{\n");
		for (VarDecl<? extends Type> globalVar : getGlobalVars()) {
			ret.append("\"var ").append(globalVar).append(" = ").append(getInitValue(globalVar)).append("\";\n");
		}
		ret.append(getMainProcess().toDot());
		ret.append("}\n");
		return ret.toString();
	}

	/*
	 * Getters
	 */

	public XcfaState getInitialState() {
		return new XcfaState(this);
	}

	public List<VarDecl<? extends Type>> getGlobalVars() {
		return List.copyOf(globalVars.keySet());
	}

	public LitExpr<?> getInitValue(VarDecl<?> varDecl) {
		return globalVars.get(varDecl);
	}

	public List<XCFAProcess> getProcesses() {
		return processes;
	}

	public XCFAProcess getMainProcess() {
		return mainProcess;
	}

	public static final class Builder {
		private final Map<VarDecl<?>, LitExpr<?>> globalVars;
		private final List<XCFAProcess> processes;
		private boolean built;
		private XCFAProcess mainProcess;

		private Builder() {
			globalVars = new LinkedHashMap<>();
			processes = new ArrayList<>();
		}

		private void checkNotBuilt() {
			checkState(!built, "An XCFA was already built.");
		}

		public void createVar(final VarDecl<?> var, LitExpr<?> initValue) {
			checkNotBuilt();
			globalVars.put(var, initValue);
		}

		public void addProcess(final XCFAProcess process) {
			checkNotBuilt();
			processes.add(process);
		}

		public XCFAProcess getMainProcess() {
			return mainProcess;
		}

		public void setMainProcess(final XCFAProcess mainProcess) {
			checkNotBuilt();
			checkArgument(processes.contains(mainProcess), "Invalid main process.");
			this.mainProcess = mainProcess;
		}

		public XCFA build() {
			checkNotBuilt();
			checkState(mainProcess != null, "Main process must be set.");
			XCFA xcfa = new XCFA(this);
			built = true;
			return xcfa;
		}

		public Map<VarDecl<?>, LitExpr<?>> getGlobalVars() {
			return globalVars;
		}
	}

}
