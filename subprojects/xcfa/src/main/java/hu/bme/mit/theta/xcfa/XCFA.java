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
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Type;

import java.util.*;

import static com.google.common.base.Preconditions.*;

/**
 * Represents an immutable Extended Control Flow Automata (XCFA). Use the builder class to
 * create a new instance.
 */
public final class XCFA {

	private final List<VarDecl<?>> vars;

	private final List<Process> processes;
	private final Process mainProcess;

	private XCFA(Builder builder) {
		vars = ImmutableList.copyOf(builder.vars);
		processes = ImmutableList.copyOf(builder.processes);
		mainProcess = builder.mainProcess;
	}

	public CFA createCFA() {
		checkState(processes.size() == 1, "XCFA cannot be converted to CFA because it has more than one process.");
		checkState(mainProcess.procedures.size() == 1, "XCFA cannot be converted to CFA because it has more than one procedure.");
		for(Process.Procedure.Edge e : mainProcess.mainProcedure.edges) {
			checkState(e.stmts.size() == 1, "XCFA cannot be converted to CFA because an edge has more/less than one statement.");
		}
		CFA.Builder builder = CFA.builder();
		CFA.Loc initLoc = null, errorLoc = null, finalLoc = null;
		for(Process.Procedure.Edge e : mainProcess.mainProcedure.edges) {
			CFA.Loc source = builder.createLoc(e.source.name);
			CFA.Loc target = builder.createLoc(e.target.name);
			builder.createEdge(source, target, e.stmts.get(0));
			if(e.source == mainProcess.mainProcedure.initLoc) initLoc = source;
			if(e.target == mainProcess.mainProcedure.errorLoc) errorLoc = target;
			else if(e.target == mainProcess.mainProcedure.finalLoc) finalLoc = target;
		}
		builder.setInitLoc(initLoc);
		builder.setErrorLoc(errorLoc);
		builder.setFinalLoc(finalLoc);
		return builder.build();
    }

	public static Builder builder() {
		return new Builder();
	}

	public List<VarDecl<?>> getVars() {
		return vars;
	}

	public List<Process> getProcesses() {
		return processes;
	}

	public Process getMainProcess() {
		return mainProcess;
	}

	public static final class Process {
		private final List<VarDecl<?>> params;

		private final List<VarDecl<?>> vars;

		private final List<Procedure> procedures;
		private final Procedure mainProcedure;

		private final String name;

		private Process(final Builder builder) {
			params = ImmutableList.copyOf(builder.params);
			vars = ImmutableList.copyOf(builder.vars);
			procedures = ImmutableList.copyOf(builder.procedures);
			mainProcedure = builder.mainProcedure;
			name = builder.name;
		}

		public static Builder builder() {
			return new Builder();
		}

		public List<VarDecl<?>> getParams() {
			return params;
		}

		public List<VarDecl<?>> getVars() {
			return vars;
		}

		public List<Procedure> getProcedures() {
			return procedures;
		}

		public Procedure getMainProcedure() {
			return mainProcedure;
		}

		public String getName() {
			return name;
		}

		public static final class Procedure {
			private final Type rtype;

			private final List<VarDecl<?>> params;

			private final List<VarDecl<?>> vars;

			private final List<Location> locs;
			private final Location initLoc;
			private final Location errorLoc;
			private final Location finalLoc;

			private final List<Edge> edges;

			private Procedure(final Builder builder) {
				rtype = builder.rtype;
				params = ImmutableList.copyOf(builder.params);
				vars = ImmutableList.copyOf(builder.vars);
				locs = ImmutableList.copyOf(builder.locs);
				initLoc = builder.initLoc;
				errorLoc = builder.errorLoc;
				finalLoc = builder.finalLoc;
				edges = ImmutableList.copyOf(builder.edges);
			}

			public static Builder builder() {
				return new Builder();
			}

			public Type getRtype() {
				return rtype;
			}

			public List<VarDecl<?>> getParams() {
				return params;
			}

			public List<VarDecl<?>> getVars() {
				return vars;
			}

			public List<Location> getLocs() {
				return locs;
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
				return edges;
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
					return incomingEdges;
				}

				public List<Edge> getOutgoingEdges() {
					return outgoingEdges;
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
					return stmts;
				}
			}

			public static final class Builder {
				private boolean built;

				private Type rtype;

				private final List<VarDecl<?>> params;

				private final List<VarDecl<?>> vars;

				private final List<Location> locs;
				private Location initLoc;
				private Location errorLoc;
				private Location finalLoc;

				private final List<Edge> edges;

				private Builder() {
					params = new ArrayList<>();
					vars = new ArrayList<>();
					locs = new ArrayList<>();
					edges = new ArrayList<>();
					built = false;
				}

				public void createParam(final VarDecl<?> param){
					checkNotBuilt();
					params.add(param);
				}

				public void createVar(final VarDecl<?> var){
					checkNotBuilt();
					vars.add(var);
				}

				public Location createLoc(final String name, final Map<String, String> dictionary){
					checkNotBuilt();
					Location loc = new Location(name, dictionary);
					locs.add(loc);
					return loc;
				}

				public void addEdge(Edge e)
				{
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
					return params;
				}

				public List<VarDecl<?>> getVars() {
					return vars;
				}

				public List<Location> getLocs() {
					return locs;
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

				public Procedure build()
				{
					checkState(initLoc != null, "Initial location must be set.");
					checkState(finalLoc != null, "Final location must be set.");
					checkState(errorLoc != null, "Error location must be set.");
					checkState(finalLoc.outgoingEdges.isEmpty(), "Final location cannot have outgoing edges.");
					checkState(errorLoc.outgoingEdges.isEmpty(), "Error location cannot have outgoing edges.");
					built = true;
					return new Procedure(this);
				}
			}
		}

		public static final class Builder {
			private boolean built;

			private final List<VarDecl<?>> params;

			private final List<VarDecl<?>> vars;

			private final List<Procedure> procedures;
			private Procedure mainProcedure;

			private String name;

			private Builder() {
				built = false;
				params = new ArrayList<>();
				vars = new ArrayList<>();
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
				vars.add(var);
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
				checkArgument(procedures.contains(mainProcedure));
				this.mainProcedure = mainProcedure;
			}

			public String getName() {
				return name;
			}

			public void setName(final String name) {
				checkNotBuilt();
				this.name = name;
			}

			public Process build()
			{
				checkNotBuilt();
				checkState(mainProcedure != null, "Main procedure must be set.");
				Process process = new Process(this);
				built = true;
				return process;
			}
		}
	}

	public static final class Builder {
		private boolean built;

		private final List<VarDecl<?>> vars;

		private final List<XCFA.Process> processes;
		private XCFA.Process mainProcess;

		private Builder() {
			vars = new ArrayList<>();
			processes = new ArrayList<>();
		}

		private void checkNotBuilt() {
			checkState(!built, "An XCFA was already built.");
		}

		public void createVar(final VarDecl<?> var) {
			checkNotBuilt();
			vars.add(var);
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
	}

}
