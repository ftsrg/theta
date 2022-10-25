/*
 *  Copyright 2022 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.xcfa.model;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.xcfa.model.utils.XcfaLabelVarReplacer;
import hu.bme.mit.theta.xcfa.model.utils.XcfaStmtUtils;

import java.util.*;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

@SuppressWarnings("unused")
public final class XcfaProcedure {
	private final String name;
	private final ImmutableMap<VarDecl<?>, Direction> params;
	private final ImmutableMap<VarDecl<?>, Optional<LitExpr<?>>> localVars;
	private final Map<Stack<XcfaLocation>, Map<VarDecl<?>, VarDecl<?>>> instantiatedVars;
	private final ImmutableList<XcfaLocation> locs;
	private final Type retType;
	private final Map<VarDecl<?>, VarDecl<?>> altVars;
	private final Map<XcfaLabel.ProcedureCallXcfaLabel, XcfaLocation> paramInitLocs;
	private final XcfaLocation initLoc;
	private final XcfaLocation errorLoc;
	private final XcfaLocation finalLoc;
	private final ImmutableList<XcfaEdge> edges;
	private final XcfaProcess parent;
	private int callCount = 0;

	private XcfaProcedure(final Builder builder, final XcfaProcess parent) {
		params = ImmutableMap.copyOf(builder.params);
		localVars = ImmutableMap.copyOf(builder.localVars);
		instantiatedVars = new LinkedHashMap<>();
		locs = ImmutableList.copyOf(builder.locs);
		locs.forEach(location -> location.setParent(this));
		altVars = builder.altVars;
		paramInitLocs = builder.paramInitLocs;
		paramInitLocs.values().forEach(loc -> loc.setParent(this));
		initLoc = builder.initLoc;
		errorLoc = builder.errorLoc;
		finalLoc = builder.finalLoc;
		edges = ImmutableList.copyOf(builder.edges);
		name = builder.name;
		retType = builder.retType;
		this.parent = parent;
	}

	public XcfaProcedure(final XcfaProcess parent, final XcfaProcedure from, final Map<VarDecl<?>, VarDecl<?>> varLut) {
		params = ImmutableMap.copyOf(from.params.entrySet().stream().map(e -> {
			final VarDecl<?> varDecl = e.getKey();
			final VarDecl<?> newVar = Var(varDecl.getName(), varDecl.getType());
			varLut.put(varDecl, newVar);
			return Map.entry(cast(newVar, varDecl.getType()), e.getValue());
		}).collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue)));
		localVars = ImmutableMap.copyOf(from.localVars.entrySet().stream().map(e -> {
			final VarDecl<?> varDecl = e.getKey();
			final VarDecl<?> newVar = Var(varDecl.getName(), varDecl.getType());
			varLut.put(varDecl, newVar);
			return Map.entry(cast(newVar, varDecl.getType()), e.getValue());
		}).collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue)));
		altVars = localVars.keySet().stream().map(var ->
			 Map.entry(var, XcfaProcedure.getAltVar(var))
		).collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue));
		final Map<XcfaLocation, XcfaLocation> locLut = new LinkedHashMap<>();
		locs = ImmutableList.copyOf(from.locs.stream().map(xcfaLocation -> {
			final XcfaLocation newLoc = XcfaLocation.copyOf(xcfaLocation);
			locLut.put(xcfaLocation, newLoc);
			return newLoc;
		}).collect(Collectors.toList()));
		locs.forEach(location -> location.setParent(this));
		paramInitLocs = new LinkedHashMap<>();
		from.paramInitLocs.forEach((callLabel, initLoc) -> paramInitLocs.put(callLabel, locLut.get(initLoc)));
		instantiatedVars = new LinkedHashMap<>();
		from.instantiatedVars.forEach((stack, localVarLut) -> {
			Stack<XcfaLocation> newStack = new Stack<>();
			stack.forEach(loc -> stack.push(locLut.get(loc)));
			Map<VarDecl<?>, VarDecl<?>> newLocalVarLut = new LinkedHashMap<>();
			localVarLut.forEach((var, localVar) -> newLocalVarLut.put(varLut.get(var), localVar));
			instantiatedVars.put(newStack, newLocalVarLut);
		});
		initLoc = locLut.get(from.initLoc);
		errorLoc = locLut.get(from.errorLoc);
		finalLoc = locLut.get(from.finalLoc);
		edges = ImmutableList.copyOf(from.edges.stream().map(xcfaEdge -> xcfaEdge.withSource(locLut.get(xcfaEdge.getSource())).withTarget(xcfaEdge.getTarget()).mapLabels(label -> XcfaStmtUtils.replacesVarsInStmt(label, varDecl -> Optional.ofNullable(varLut.get(varDecl)).map(varDecl1 -> cast(varDecl1, varDecl.getType()))).orElse(label))).collect(Collectors.toList()));
		for (XcfaEdge edge : edges) {
			edge.getTarget().addIncomingEdge(edge);
			edge.getSource().addOutgoingEdge(edge);
		}
		name = from.name;
		retType = from.retType;
		this.parent = parent;
	}

	public static Builder builder() {
		return new Builder();
	}

	public String toDot(Collection<String> cexLocations, Collection<XcfaEdge> cexEdges) {
		StringBuilder ret = new StringBuilder("label=\"");
		ret.append(name).append("(");
		params.forEach((varDecl, direction) -> {
			ret.append(direction).append(" ");
			ret.append(varDecl);
			ret.append(",");
		});
		ret.append(")\"\n");
		ret.append("\"").append(name).append(" vars: {");
		localVars.forEach((varDecl, litExpr) -> {
			ret.append(varDecl);
			if (litExpr.isPresent()) {
				ret.append(" = ").append(litExpr);
			}
			ret.append(",");
		});
		ret.append("}\";\n");
		for (XcfaLocation location : getLocs()) {
			ret.append("\"").append(location.getName()).append("\"");
			if (cexLocations.contains(location.getName())) ret.append(("[color=red]"));
			else if (location.isErrorLoc()) ret.append("[xlabel=err]");
			else if (location.isEndLoc()) ret.append("[xlabel=final]");
			else if (getInitLoc() == location) ret.append("[xlabel=start]");
			ret.append(";\n");
		}
		for (XcfaEdge edge : getEdges()) {
			ret.append("\"").append(edge.getSource().getName()).append("\" -> ");
			ret.append("\"").append(edge.getTarget().getName()).append("\" [label=\"");
			for (XcfaLabel label : edge.getLabels()) {
				ret.append(label.toString());
				ret.append(", ");
			}
			ret.append("\"");
			if (cexEdges.contains(edge)) {
				ret.append(",color=red");
			}
			ret.append("];\n");
		}
		return ret.toString();
	}

	public Map<VarDecl<?>, Direction> getParams() {
		return params;
	}

	public List<VarDecl<?>> getLocalVars() {
		return List.copyOf(localVars.keySet());
	}

	public Map<VarDecl<?>, Optional<LitExpr<?>>> getLocalVarMap() {
		return localVars;
	}

	public Optional<LitExpr<?>> getInitValue(VarDecl<?> varDecl) {
		return localVars.get(varDecl);
	}

	public List<XcfaLocation> getLocs() {
		return locs;
	}

	public XcfaLocation getParamInitLoc(XcfaLabel.ProcedureCallXcfaLabel callLabel) {
		return paramInitLocs.get(callLabel);
	}

	public Map<VarDecl<?>, VarDecl<?>> getAltVars() {
		return altVars;
	}

	public XcfaLocation getInitLoc() {
		return initLoc;
	}

	public XcfaLocation getErrorLoc() {
		return errorLoc;
	}

	public XcfaLocation getFinalLoc() {
		return finalLoc;
	}

	public List<XcfaEdge> getEdges() {
		return edges;
	}

	public String getName() {
		return name;
	}

	@Override
	public String toString() {
		return name;
	}

	public XcfaProcess getParent() {
		return parent;
	}

	public Type getRetType() {
		return retType;
	}

	public XcfaProcedure duplicate(final XcfaProcess parent, final Map<VarDecl<?>, VarDecl<?>> varLut) {
		return new XcfaProcedure(parent, this, varLut);
	}

	public Map<VarDecl<?>, VarDecl<?>> getInstantiatedVars(Stack<XcfaLocation> locationStack) {
		Map<VarDecl<?>, VarDecl<?>> varLut = instantiatedVars.get(locationStack);
		if (varLut == null) {
			varLut = new LinkedHashMap<>();
			for (VarDecl<?> var : getLocalVarMap().keySet()) {
				varLut.put(var, Var(var.getName() + "@" + callCount, var.getType()));
			}
			++callCount;
			instantiatedVars.put(locationStack, varLut);
		}
		return varLut;
	}

	private static VarDecl<?> getAltVar(VarDecl<?> var) {
		return Var(var.getName() + "'", var.getType());
	}

	public static final class Builder {
		private static final String RESULT_NAME = "result";

		private final LinkedHashMap<VarDecl<?>, Direction> params;
		private final Map<VarDecl<?>, Optional<LitExpr<?>>> localVars;
		private final Map<VarDecl<?>, VarDecl<?>> altVars;
		private final List<XcfaLocation> locs;
		private final List<XcfaEdge> edges;
		private Type retType;
		private String name;
		private final Map<XcfaLabel.ProcedureCallXcfaLabel, XcfaLocation> paramInitLocs;
		private XcfaLocation initLoc;
		private XcfaLocation errorLoc;
		private XcfaLocation finalLoc;

		private XcfaProcedure built = null;

		private Builder() {
			params = new LinkedHashMap<>();
			localVars = new LinkedHashMap<>();
			altVars = new LinkedHashMap<>();
			paramInitLocs = new LinkedHashMap<>();
			locs = new ArrayList<>();
			edges = new ArrayList<>();
		}

		public String toDot(Collection<String> cexLocations, Collection<XcfaEdge> cexEdges) {
			StringBuilder ret = new StringBuilder("label=\"");
			ret.append(name).append("(");
			params.forEach((varDecl, direction) -> {
				ret.append(direction).append(" ");
				ret.append(varDecl);
				ret.append(",");
			});
			ret.append(")\"\n");
			ret.append("\"").append(name).append(" vars: {");
			localVars.forEach((varDecl, litExpr) -> {
				ret.append(varDecl);
				if (litExpr.isPresent()) {
					ret.append(" = ").append(litExpr);
				}
				ret.append(",");
			});
			ret.append("}\";\n");
			for (XcfaLocation location : getLocs()) {
				ret.append("\"").append(location.getName()).append("\"");
				if (cexLocations.contains(location.getName())) ret.append(("[color=red]"));
				else if (location.isErrorLoc()) ret.append("[xlabel=err]");
				else if (location.isEndLoc()) ret.append("[xlabel=final]");
				else if (getInitLoc() == location) ret.append("[xlabel=start]");
				ret.append(";\n");
			}
			for (XcfaEdge edge : getEdges()) {
				ret.append("\"").append(edge.getSource().getName()).append("\" -> ");
				ret.append("\"").append(edge.getTarget().getName()).append("\" [label=\"");
				for (XcfaLabel label : edge.getLabels()) {
					ret.append(label.toString());
					ret.append(", ");
				}
				ret.append("\"");
				if (cexEdges.contains(edge)) {
					ret.append(",color=red");
				}
				ret.append("];\n");
			}
			return ret.toString();
		}

		private void checkNotBuilt() {
			checkState(built == null, "A Procedure was already built.");
		}


		// params
		public LinkedHashMap<VarDecl<?>, Direction> getParams() {
			return params;
		}

		public void createParam(final Direction direction, final VarDecl<?> param) {
			checkNotBuilt();
			params.put(param, direction);
		}

		public void addParamInitLoc(XcfaLabel.ProcedureCallXcfaLabel callLabel, XcfaProcedure.Builder callingProcedure) {
			checkNotBuilt();

			List<XcfaLabel> paramAssignments = new ArrayList<>();
			int i = 0;
			for (Map.Entry<VarDecl<?>, Direction> entry : params.entrySet()) {
				if (entry.getValue() != Direction.OUT)
					paramAssignments.add(XcfaLabel.Stmt(AssignStmt.create(entry.getKey(), XcfaLabelVarReplacer.replaceVars(callLabel.getParams().get(i), callingProcedure.altVars))));
				++i;
			}
			if (paramAssignments.isEmpty()) {
				paramInitLocs.put(callLabel, initLoc);
			} else {
				XcfaLocation paramLoc = XcfaLocation.uniqeCopyOf(initLoc);
				addLoc(paramLoc);
				addEdge(XcfaEdge.of(paramLoc, initLoc, paramAssignments));
				paramInitLocs.put(callLabel, paramLoc);
			}
		}

		// localVars
		public Map<VarDecl<?>, Optional<LitExpr<?>>> getLocalVars() {
			return localVars;
		}

		public void createVar(final VarDecl<?> var, final LitExpr<?> initValue) {
			checkNotBuilt();
			localVars.put(var, Optional.ofNullable(initValue));
			altVars.put(var, XcfaProcedure.getAltVar(var));
		}

		public void removeVar(final VarDecl<?> var) {
			localVars.remove(var);
			altVars.remove(var);
		}

		// rtype
		public void setRetType(Type retType) {
			this.retType = retType;
		}

		public Type getRetType() {
			return retType;
		}

		// locs
		public List<XcfaLocation> getLocs() {
			return locs;
		}

		public void removeLoc(XcfaLocation loc) {
			checkArgument(loc != initLoc, "Cannot remove initloc!");
			checkArgument(loc != finalLoc, "Cannot remove finalloc!");
			checkArgument(loc != errorLoc, "Cannot remove errorloc!");
			locs.remove(loc);
		}

		public XcfaLocation addLoc(XcfaLocation loc) {
			checkNotBuilt();
			if (!locs.contains(loc)) {
				checkState(locs.stream().noneMatch(l -> l.getName().equals(loc.getName())));
				checkArgument(loc.getIncomingEdges().size() == 0 && loc.getOutgoingEdges().size() == 0, "Loc already part of an XCFA procedure!");
				locs.add(loc);
			}
			return loc;
		}

		// edges
		public List<XcfaEdge> getEdges() {
			return edges;
		}

		public void addEdge(XcfaEdge e) {
			checkNotBuilt();
			checkArgument(locs.contains(e.getSource()), "Invalid source.");
			checkArgument(locs.contains(e.getTarget()), "Invalid target.");
			if (!edges.contains(e)) {
				edges.add(e);
				e.getSource().addOutgoingEdge(e);
				e.getTarget().addIncomingEdge(e);
			}
		}

		// name
		public String getName() {
			return name;
		}

		public void setName(String name) {
			this.name = name;
		}

		// initLoc
		public XcfaLocation getInitLoc() {
			return initLoc;
		}

		public void setInitLoc(final XcfaLocation initLoc) {
			checkNotBuilt();
			checkArgument(locs.contains(initLoc), "Init location not present in XCFA.");
			checkArgument(!initLoc.equals(errorLoc), "Init location cannot be the same as error location.");
			checkArgument(finalLoc == null || !finalLoc.equals(initLoc), "Init location cannot be the same as final location.");
			this.initLoc = initLoc;
		}

		// errorLoc
		public XcfaLocation getErrorLoc() {
			return errorLoc;
		}

		public void setErrorLoc(final XcfaLocation errorLoc) {
			checkNotBuilt();
			checkArgument(locs.contains(errorLoc), "Error location not present in XCFA.");
			checkArgument(initLoc == null || !initLoc.equals(errorLoc), "Error location cannot be the same as init location.");
			checkArgument(finalLoc == null || !finalLoc.equals(errorLoc), "Error location cannot be the same as final location.");
			if (errorLoc != null) errorLoc.setErrorLoc(true);
			else this.errorLoc.setErrorLoc(false);
			this.errorLoc = errorLoc;
		}

		// finalLoc
		public XcfaLocation getFinalLoc() {
			return finalLoc;
		}

		public void setFinalLoc(final XcfaLocation finalLoc) {
			checkNotBuilt();
			checkArgument(locs.contains(finalLoc), "Final location not present in XCFA.");
			checkArgument(!finalLoc.equals(errorLoc), "Final location cannot be the same as error location.");
			checkArgument(initLoc == null || !initLoc.equals(finalLoc), "Final location cannot be the same as init location.");
			this.finalLoc = finalLoc;
			finalLoc.setEndLoc(true);
		}

		public XcfaProcedure build(XcfaProcess process) {
			if (built != null) return built;

			checkState(initLoc != null, "Initial location must be set.");
			checkState(finalLoc != null, "Final location must be set.");
			checkState(finalLoc.getOutgoingEdges().isEmpty(), "Final location cannot have outgoing edges.");
			if (errorLoc != null)
				checkState(errorLoc.getOutgoingEdges().isEmpty(), "Error location cannot have outgoing edges.");
			XcfaProcedure procedure = new XcfaProcedure(this, process);
			built = procedure;
			return procedure;
		}

		public void removeEdge(XcfaEdge xcfaEdge) {
			edges.remove(xcfaEdge);
			xcfaEdge.getTarget().removeIncomingEdge(xcfaEdge);
			xcfaEdge.getSource().removeOutgoingEdge(xcfaEdge);
		}
	}

	public enum Direction {
		IN,
		OUT,
		INOUT
	}
}