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
import com.google.common.collect.ImmutableSet;
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

	private final Collection<VarDecl<?>> vars;

	private final Collection<Process> processes;
	private final Process mainProcess;

	private XCFA(Builder builder) {
		vars = ImmutableSet.copyOf(builder.vars);
		processes = ImmutableSet.copyOf(builder.processes);
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

	public Collection<VarDecl<?>> getVars() {
		return vars;
	}

	public Collection<Process> getProcesses() {
		return processes;
	}

	public Process getMainProcess() {
		return mainProcess;
	}

	public static final class Process {
		private final List<VarDecl<?>> params;

		private final Collection<VarDecl<?>> vars;

		private final Collection<Procedure> procedures;
		private final Procedure mainProcedure;

		private final String name;

		private Process(final Builder builder) {
			params = ImmutableList.copyOf(builder.params);
			vars = ImmutableSet.copyOf(builder.vars);
			procedures = ImmutableSet.copyOf(builder.procedures);
			mainProcedure = builder.mainProcedure;
			name = builder.name;
		}

		public Builder builder() {
			return new Builder();
		}

		public List<VarDecl<?>> getParams() {
			return params;
		}

		public Collection<VarDecl<?>> getVars() {
			return vars;
		}

		public Collection<Procedure> getProcedures() {
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

			private final Collection<VarDecl<?>> vars;

			private final Collection<Location> locs;
			private final Location initLoc;
			private final Location errorLoc;
			private final Location finalLoc;

			private final Collection<Edge> edges;

			private Procedure(final Builder builder) {
				rtype = builder.rtype;
				params = ImmutableList.copyOf(builder.params);
				vars = ImmutableSet.copyOf(builder.vars);
				locs = ImmutableSet.copyOf(builder.locs);
				initLoc = builder.initLoc;
				errorLoc = builder.errorLoc;
				finalLoc = builder.finalLoc;
				edges = ImmutableSet.copyOf(builder.edges);
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

			public Collection<VarDecl<?>> getVars() {
				return vars;
			}

			public Collection<Location> getLocs() {
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

			public Collection<Edge> getEdges() {
				return edges;
			}

			public static final class Location {
				private final String name;

				private final Map<String, String> dictionary;

				private final Collection<Edge> incomingEdges;
				private final Collection<Edge> outgoingEdges;

				private Location(final String name, final Map<String, String> dictionary) {
					this.name = checkNotNull(name);
					this.dictionary = dictionary;
					outgoingEdges = new HashSet<>();
					incomingEdges = new HashSet<>();
				}

				public String getName() {
					return name;
				}

				public Map<String, String> getDictionary() {
					return dictionary;
				}

				public Collection<Edge> getIncomingEdges() {
					return incomingEdges;
				}

				public Collection<Edge> getOutgoingEdges() {
					return outgoingEdges;
				}
			}

			public static final class Edge {
				private final Location source;
				private final Location target;

				private final List<Stmt> stmts;

				private Edge(final Location source, final Location target, final List<Stmt> stmts) {
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

				private List<VarDecl<?>> params;

				private Collection<VarDecl<?>> vars;

				private Collection<Location> locs;
				private Location initLoc;
				private Location errorLoc;
				private Location finalLoc;

				private Collection<Edge> edges;

				private Builder() {
					params = new ArrayList<>();
					vars = new HashSet<>();
					locs = new HashSet<>();
					edges = new HashSet<>();
					built = false;
				}

				public VarDecl<?> createParam(final VarDecl<?> param){
					checkNotBuilt();
					params.add(param);
					return param;
				}

				public VarDecl<?> createVar(final VarDecl<?> var){
					checkNotBuilt();
					vars.add(var);
					return var;
				}

				public Location createLoc(final String name, final Map<String, String> dictionary){
					checkNotBuilt();
					Location loc = new Location(name, dictionary);
					locs.add(loc);
					return loc;
				}

				public Edge createEdge(final Location source, final Location target, final List<Stmt> stmts)
				{
					checkNotBuilt();
					checkArgument(locs.contains(source), "Invalid source.");
					checkArgument(locs.contains(target), "Invalid target.");
					Edge edge = new Edge(source, target, stmts);
					edges.add(edge);
					return edge;
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

				public Collection<VarDecl<?>> getVars() {
					return vars;
				}

				public Collection<Location> getLocs() {
					return locs;
				}

				public Location getInitLoc() {
					return initLoc;
				}

				public void setInitLoc(final Location initLoc) {
					checkNotBuilt();
					checkArgument(locs.contains(initLoc), "Init location not present in XCFA.");
					checkArgument(!errorLoc.equals(initLoc), "Init location cannot be the same as error location.");
					checkArgument(!finalLoc.equals(initLoc), "Init location cannot be the same as final location.");
					this.initLoc = initLoc;
				}

				public Location getErrorLoc() {
					return errorLoc;
				}

				public void setErrorLoc(final Location errorLoc) {
					checkNotBuilt();
					checkArgument(locs.contains(errorLoc), "Error location not present in XCFA.");
					checkArgument(!initLoc.equals(errorLoc), "Error location cannot be the same as init location.");
					checkArgument(!finalLoc.equals(errorLoc), "Error location cannot be the same as final location.");
					this.errorLoc = errorLoc;
				}

				public Location getFinalLoc() {
					return finalLoc;
				}

				public void setFinalLoc(final Location finalLoc) {
					checkNotBuilt();
					checkArgument(locs.contains(finalLoc), "Final location not present in XCFA.");
					checkArgument(!errorLoc.equals(finalLoc), "Final location cannot be the same as error location.");
					checkArgument(!initLoc.equals(finalLoc), "Final location cannot be the same as init location.");
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

			private List<VarDecl<?>> params;

			private Collection<VarDecl<?>> vars;

			private Collection<Procedure> procedures;
			private Procedure mainProcedure;

			private String name;

			private Builder() {
				built = false;
				params = new ArrayList<>();
				vars = new HashSet<>();
				procedures = new HashSet<>();
			}

			private void checkNotBuilt() {
				checkState(!built, "A Process was already built.");
			}

			private VarDecl<?> createParam(final VarDecl<?> param) {
				checkNotBuilt();
				params.add(param);
				return param;
			}

			private VarDecl<?> createVar(final VarDecl<?> var) {
				checkNotBuilt();
				vars.add(var);
				return var;
			}

			private void addProcedure(final Procedure procedure)
			{
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

		private Collection<VarDecl<?>> vars;

		private Collection<XCFA.Process> processes;
		private XCFA.Process mainProcess;

		private Builder() {
			vars = new HashSet<>();
			processes = new HashSet<>();
		}

		private void checkNotBuilt() {
			checkState(!built, "An XCFA was already built.");
		}

		public VarDecl<?> createVar(final VarDecl<?> var) {
			checkNotBuilt();
			vars.add(var);
			return var;
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
