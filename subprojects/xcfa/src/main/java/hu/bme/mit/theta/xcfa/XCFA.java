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
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Type;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

/**
 * Represents an immutable Extended Control Flow Automata (XCFA). Use the builder class to
 * create a new instance.
 *
 * TODO type checks around parameters and return value passing
 *   This would be useful for CallUtils, where there are multiple unchecked casts.
 */
public final class XCFA {

	private final List<VarDecl<? extends Type>> globalVars;

	private final List<Process> processes;
	private final Process mainProcess;

	private XCFA(Builder builder) {
		globalVars = ImmutableList.copyOf(builder.globalVars);
		processes = ImmutableList.copyOf(builder.processes);
		mainProcess = builder.mainProcess;
	}

	public static Builder builder() {
		return new Builder();
	}

	public CFA createCFA() {
		checkState(processes.size() == 1, "XCFA cannot be converted to CFA because it has more than one process.");
		checkState(mainProcess.procedures.size() == 1, "XCFA cannot be converted to CFA because it has more than one procedure.");
		CFA.Builder builder = CFA.builder();
		CFA.Loc initLoc = null, errorLoc = null, finalLoc = null;
		for (Process.Procedure.Edge e : mainProcess.mainProcedure.edges) {
			List<CFA.Loc> locations = new ArrayList<>();
			locations.add(builder.createLoc(e.source.name));
			for (int i = 1; i < e.getStmts().size(); ++i)
				locations.add(builder.createLoc(""));
			locations.add(builder.createLoc(e.target.name));
			for (int i = 0; i < e.getStmts().size(); ++i)
				builder.createEdge(locations.get(i), locations.get(i + 1), e.stmts.get(i));
			if (e.source == mainProcess.mainProcedure.initLoc) initLoc = locations.get(0);
			if (e.target == mainProcess.mainProcedure.errorLoc) errorLoc = locations.get(locations.size() - 1);
			else if (e.target == mainProcess.mainProcedure.finalLoc) finalLoc = locations.get(locations.size() - 1);
		}
		builder.setInitLoc(initLoc);
		builder.setErrorLoc(errorLoc);
		builder.setFinalLoc(finalLoc);
		return builder.build();
	}

	public List<VarDecl<? extends Type>> getGlobalVars() {
		return Collections.unmodifiableList(globalVars);
	}

	public List<Process> getProcesses() {
		return Collections.unmodifiableList(processes);
	}

	public Process getMainProcess() {
		return mainProcess;
	}

	public static final class Process {
		private final List<VarDecl<?>> params;

		private final List<VarDecl<?>> threadLocalVars;

		private final List<Procedure> procedures;
		private final Procedure mainProcedure;
		private static final String LABEL = "process";

		private final String name;

		private Process(final Builder builder) {
			params = ImmutableList.copyOf(builder.params);
			threadLocalVars = ImmutableList.copyOf(builder.threadLocalVars);
			procedures = ImmutableList.copyOf(builder.procedures);
			mainProcedure = builder.mainProcedure;
			name = builder.name;
		}

		public static Builder builder() {
			return new Builder();
		}

		public List<VarDecl<?>> getParams() {
			return Collections.unmodifiableList(params);
		}

		public List<VarDecl<?>> getThreadLocalVars() {
			return Collections.unmodifiableList(threadLocalVars);
		}

		public List<Procedure> getProcedures() {
			return Collections.unmodifiableList(procedures);
		}

		public Procedure getMainProcedure() {
			return mainProcedure;
		}

		public String getName() {
			return name;
		}

		@Override
		public String toString() {
			return Utils.lispStringBuilder().add(LABEL).add(name).toString();
		}

        public static final class Procedure {
			private final String name;
			private final Type rtype;
			private final VarDecl<? extends Type> result;

			private final List<VarDecl<?>> params;

			private final List<VarDecl<?>> localVars;

			private final List<Location> locs;
			private final Location initLoc;
			private final Location errorLoc;
			private final Location finalLoc;

			private final List<Edge> edges;

			private Procedure(final Builder builder) {
				rtype = builder.rtype;
				params = ImmutableList.copyOf(builder.params);
				localVars = ImmutableList.copyOf(builder.localVars);
				locs = ImmutableList.copyOf(builder.locs);
				initLoc = builder.initLoc;
				errorLoc = builder.errorLoc;
				finalLoc = builder.finalLoc;
				edges = ImmutableList.copyOf(builder.edges);
				result = builder.result;
				name = builder.name;
			}

			public static Builder builder() {
				return new Builder();
			}

			public Type getRtype() {
				return rtype;
			}

			public List<VarDecl<?>> getParams() {
				return Collections.unmodifiableList(params);
			}

			public List<VarDecl<?>> getLocalVars() {
				return Collections.unmodifiableList(localVars);
			}

			public List<Location> getLocs() {
				return Collections.unmodifiableList(locs);
			}

			public Location getInitLoc() {
				return initLoc;
			}

			public Location getErrorLoc() {
				return errorLoc;
			}

			public Location getFinalLoc() {
				return finalLoc;
			}

			public List<Edge> getEdges() {
				return Collections.unmodifiableList(edges);
			}

			public VarDecl<? extends Type> getResult() {
				return result;
			}

			public String getName() {
				return name;
			}

			@Override
			public String toString() {
				return name;
			}

			public static final class Location {
				private final String name;

				private final Map<String, String> dictionary;

				private final List<Edge> incomingEdges;
				private final List<Edge> outgoingEdges;

				public Location(final String name, final Map<String, String> dictionary) {
					this.name = checkNotNull(name);
					this.dictionary = dictionary;
					outgoingEdges = new ArrayList<>();
					incomingEdges = new ArrayList<>();
				}

				public String getName() {
					return name;
				}

				public Map<String, String> getDictionary() {
					return dictionary;
				}

				public List<Edge> getIncomingEdges() {
					return Collections.unmodifiableList(incomingEdges);
				}

				public List<Edge> getOutgoingEdges() {
					return Collections.unmodifiableList(outgoingEdges);
				}

				@Override
				public String toString() {
					return name;
				}
			}

			public static final class Edge {
				private final Location source;
				private final Location target;

				private final List<Stmt> stmts;

				public Edge(final Location source, final Location target, final List<Stmt> stmts) {
					this.source = checkNotNull(source);
					this.target = checkNotNull(target);
					this.stmts = ImmutableList.copyOf(stmts);
					source.outgoingEdges.add(this);
					target.incomingEdges.add(this);
				}

				public Location getSource() {
					return source;
				}

				public Location getTarget() {
					return target;
				}

				public List<Stmt> getStmts() {
					return Collections.unmodifiableList(stmts);
				}

				@Override
				public String toString() {
					return Utils.lispStringBuilder("Edge").add(
							Utils.lispStringBuilder("Source").add(source)
					).add(
							Utils.lispStringBuilder("Target").add(target)
					).add(
							Utils.lispStringBuilder("Stmts").addAll(stmts)
					).toString();
				}
			}

			public static final class Builder {
				/* result is a special variable name, which contains the value that
				 * will be returned to the caller function.
				 * Currently *_RES_VAR is understood as a result variable.
				 * This is because Gazer uses this too.
				 */
				private static final String RESULT_NAME = "result";
				private final List<VarDecl<?>> params;
				private final List<VarDecl<?>> localVars;
				private final List<Location> locs;
				private final List<Edge> edges;
				private boolean built;
				private String name;
				private Type rtype;
				private VarDecl<?> result;
				private Location initLoc;
				private Location errorLoc;
				private Location finalLoc;

				private boolean isResultVariable(String varName) {
					// the first is for Gazer
					return varName.endsWith("RES_VAR") || varName.equals(RESULT_NAME);
				}

				private Builder() {
					params = new ArrayList<>();
					localVars = new ArrayList<>();
					locs = new ArrayList<>();
					edges = new ArrayList<>();
					built = false;
				}

				public void createParam(final VarDecl<?> param) {
					checkNotBuilt();
					params.add(param);
				}

				public void createVar(final VarDecl<?> var) {
					checkNotBuilt();
					if (isResultVariable(var.getName())) setResult(var);
					localVars.add(var);
				}

				public Location addLoc(Location loc) {
					checkNotBuilt();
					locs.add(loc);
					return loc;
				}

				public void addEdge(Edge e) {
					checkNotBuilt();
					checkArgument(locs.contains(e.source), "Invalid source.");
					checkArgument(locs.contains(e.target), "Invalid target.");
					edges.add(e);
				}

				private void checkNotBuilt() {
					checkState(!built, "A Procedure was already built.");
				}

				public Type getRtype() {
					return rtype;
				}

				public void setRtype(final Type rtype) {
					this.rtype = rtype;
				}

				public List<VarDecl<?>> getParams() {
					return Collections.unmodifiableList(params);
				}

				public List<VarDecl<?>> getLocalVars() {
					return Collections.unmodifiableList(localVars);
				}

				public List<Location> getLocs() {
					return Collections.unmodifiableList(locs);
				}

				public Location getInitLoc() {
					return initLoc;
				}

				public void setInitLoc(final Location initLoc) {
					checkNotBuilt();
					checkArgument(locs.contains(initLoc), "Init location not present in XCFA.");
					//checkArgument(!errorLoc.equals(initLoc), "Init location cannot be the same as error location.");
					checkArgument(finalLoc == null || !finalLoc.equals(initLoc), "Init location cannot be the same as final location.");
					this.initLoc = initLoc;
				}

				public Location getErrorLoc() {
					return errorLoc;
				}

				public void setErrorLoc(final Location errorLoc) {
					checkNotBuilt();
					checkArgument(locs.contains(errorLoc), "Error location not present in XCFA.");
					checkArgument(initLoc == null || !initLoc.equals(errorLoc), "Error location cannot be the same as init location.");
					checkArgument(finalLoc == null || !finalLoc.equals(errorLoc), "Error location cannot be the same as final location.");
					this.errorLoc = errorLoc;
				}

				public Location getFinalLoc() {
					return finalLoc;
				}

				public void setFinalLoc(final Location finalLoc) {
					checkNotBuilt();
					checkArgument(locs.contains(finalLoc), "Final location not present in XCFA.");
					//checkArgument(!errorLoc.equals(finalLoc), "Final location cannot be the same as error location.");
					checkArgument(initLoc == null || !initLoc.equals(finalLoc), "Final location cannot be the same as init location.");
					this.finalLoc = finalLoc;
				}

				public Procedure build() {
					checkState(initLoc != null, "Initial location must be set.");
					checkState(finalLoc != null, "Final location must be set.");
					//checkState(errorLoc != null, "Error location must be set."); //TODO:
					checkState(finalLoc.outgoingEdges.isEmpty(), "Final location cannot have outgoing edges.");
					//checkState(errorLoc.outgoingEdges.isEmpty(), "Error location cannot have outgoing edges.");
					built = true;
					return new Procedure(this);
				}

				public void setResult(VarDecl<?> result) {
					this.result = result;
				}

				public String getName() {
					return name;
				}

				public void setName(String name) {
					this.name = name;
				}
			}
		}

		public static final class Builder {
			private final List<VarDecl<?>> params;
			private final List<VarDecl<?>> threadLocalVars;
			private final List<Procedure> procedures;
			private boolean built;
			private Procedure mainProcedure;

			private String name;

			private Builder() {
				built = false;
				params = new ArrayList<>();
				threadLocalVars = new ArrayList<>();
				procedures = new ArrayList<>();
			}

			private void checkNotBuilt() {
				checkState(!built, "A Process was already built.");
			}

			public void createParam(final VarDecl<?> param) {
				checkNotBuilt();
				params.add(param);
			}

			public void createVar(final VarDecl<?> var) {
				checkNotBuilt();
				threadLocalVars.add(var);
			}

			public void addProcedure(final Procedure procedure) {
				checkNotBuilt();
				procedures.add(procedure);
			}

			public Procedure getMainProcedure() {
				return mainProcedure;
			}

			public void setMainProcedure(final Procedure mainProcedure) {
				checkNotBuilt();
				checkArgument(procedures.contains(mainProcedure), "Procedures does not contain main procedure");
				this.mainProcedure = mainProcedure;
			}

			public String getName() {
				return name;
			}

			public void setName(final String name) {
				checkNotBuilt();
				this.name = name;
			}

			public Process build() {
				checkNotBuilt();
				checkState(mainProcedure != null, "Main procedure must be set.");
				Process process = new Process(this);
				built = true;
				return process;
			}
		}
	}

	public static final class Builder {
		private final List<VarDecl<?>> globalVars;
		private final List<XCFA.Process> processes;
		private boolean built;
		private XCFA.Process mainProcess;

		private Builder() {
			globalVars = new ArrayList<>();
			processes = new ArrayList<>();
		}

		private void checkNotBuilt() {
			checkState(!built, "An XCFA was already built.");
		}

		public void createVar(final VarDecl<?> var) {
			checkNotBuilt();
			globalVars.add(var);
		}

		public void addProcess(final Process process) {
			checkNotBuilt();
			processes.add(process);
		}

		public Process getMainProcess() {
			return mainProcess;
		}

		public void setMainProcess(final Process mainProcess) {
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

		public List<VarDecl<? extends Type>> getGlobalVars() {
			return globalVars;
		}
	}

}
