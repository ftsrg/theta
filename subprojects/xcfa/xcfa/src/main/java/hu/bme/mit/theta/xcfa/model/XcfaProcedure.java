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
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.xcfa.passes.XcfaPassManager;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;

@SuppressWarnings("unused")
public final class XcfaProcedure {
    private final String name;
    private final ImmutableMap<VarDecl<?>, Direction> params;
    private final ImmutableMap<VarDecl<?>, Optional<LitExpr<?>>> localVars;
    private final ImmutableList<XcfaLocation> locs;
    private final Type retType;
    private final XcfaLocation initLoc;
    private final XcfaLocation errorLoc;
    private final XcfaLocation finalLoc;
    private final ImmutableList<XcfaEdge> edges;
    private XcfaProcess parent;

    private XcfaProcedure(final Builder builder) {
        params = ImmutableMap.copyOf(builder.params);
        localVars = ImmutableMap.copyOf(builder.localVars);
        locs = ImmutableList.copyOf(builder.locs);
        locs.forEach(location -> location.setParent(this));
        initLoc = builder.initLoc;
        errorLoc = builder.errorLoc;
        finalLoc = builder.finalLoc;
        edges = ImmutableList.copyOf(builder.edges);
        edges.forEach(edge -> edge.setParent(this));
        name = builder.name;
        retType = builder.retType;
    }

    public XcfaProcedure(XcfaProcedure procedure) {
        this(procedure, new LinkedHashMap<>());
    }

    public XcfaProcedure(XcfaProcedure procedure, Map<VarDecl<?>, VarDecl<?>> newVarLut) {
        XcfaMetadata.lookupMetadata(procedure).forEach((s, o) -> {
            XcfaMetadata.create(this, s, o);
        });
        parent = null; // ProcessBuilder will fill out this field

        Map<VarDecl<?>, Direction> paramCollectList = new LinkedHashMap<>();
        procedure.params.forEach((varDecl, direction) -> {
            VarDecl<?> newVar = VarDecl.copyOf(varDecl);
            paramCollectList.put(newVar, direction);
            newVarLut.put(varDecl, newVar);
        });
        params = ImmutableMap.copyOf(paramCollectList);

        Map<VarDecl<?>, Optional<LitExpr<?>>> localVarsCollectList = new HashMap<>();
        procedure.localVars.forEach((varDecl, litExpr) -> {
            VarDecl<?> newVar = newVarLut.containsKey(varDecl) ? newVarLut.get(varDecl) : VarDecl.copyOf(varDecl);
            localVarsCollectList.put(newVar, litExpr);
            newVarLut.put(varDecl, newVar);
        });
        localVars = ImmutableMap.copyOf(localVarsCollectList);

        Map<XcfaLocation, XcfaLocation> newLocLut = new HashMap<>();

        List<XcfaLocation> locsCollectList = new ArrayList<>();
        procedure.locs.forEach(loc -> {
            XcfaLocation location = XcfaLocation.copyOf(loc);
            XcfaMetadata.lookupMetadata(loc).forEach((s, o) -> {
                XcfaMetadata.create(location, s, o);
            });
            locsCollectList.add(location);
            newLocLut.put(loc, location);
        });
        locs = ImmutableList.copyOf(locsCollectList);
        locs.forEach(location -> location.setParent(this));

        initLoc = newLocLut.get(procedure.initLoc);
        errorLoc = newLocLut.get(procedure.errorLoc);
        if(errorLoc != null) errorLoc.setErrorLoc(true);
        finalLoc = newLocLut.get(procedure.finalLoc);
        if(finalLoc != null) finalLoc.setEndLoc(true);

        List<XcfaEdge> edgeCollectList = new ArrayList<>();
        procedure.edges.forEach(edge -> {
            XcfaEdge xcfaEdge = XcfaEdge.copyOf(edge, newLocLut, newVarLut);
            XcfaMetadata.lookupMetadata(edge).forEach((s, o) -> {
                XcfaMetadata.create(xcfaEdge, s, o);
            });
            edgeCollectList.add(xcfaEdge);
        });
        edges = ImmutableList.copyOf(edgeCollectList);
        edges.forEach(edge -> edge.setParent(this));

        name = procedure.name;
        retType = procedure.retType;
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
            if(cexLocations.contains(location.getName())) ret.append(("[color=red]"));
            else if (location.isErrorLoc()) ret.append("[xlabel=err]");
            else if (location.isEndLoc()) ret.append("[xlabel=final]");
            else if (getInitLoc() == location) ret.append("[xlabel=start]");
            ret.append(";\n");
        }
        for (XcfaEdge edge : getEdges()) {
            ret.append("\"").append(edge.getSource().getName()).append("\" -> ");
            ret.append("\"").append(edge.getTarget().getName()).append("\" [label=\"");
            for (Stmt stmt : edge.getStmts()) {
                ret.append(stmt.toString());
                ret.append(", ");
            }
            ret.append("\"");
            if(cexEdges.contains(edge)) {
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

    public Optional<LitExpr<?>> getInitValue(VarDecl<?> varDecl) {
        return localVars.get(varDecl);
    }

    public List<XcfaLocation> getLocs() {
        return locs;
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

    void setParent(XcfaProcess xcfaProcess) {
        this.parent = xcfaProcess;
    }

    public static final class Builder {
        private static final String RESULT_NAME = "result";

        private final LinkedHashMap<VarDecl<?>, Direction> params;
        private final Map<VarDecl<?>, Optional<LitExpr<?>>> localVars;
        private final List<XcfaLocation> locs;
        private final List<XcfaEdge> edges;
        private Type retType;
        private String name;
        private XcfaLocation initLoc;
        private XcfaLocation errorLoc;
        private XcfaLocation finalLoc;

        private boolean built;

        private Builder() {
            params = new LinkedHashMap<>();
            localVars = new HashMap<>();
            locs = new ArrayList<>();
            edges = new ArrayList<>();
            built = false;
        }

        private void checkNotBuilt() {
            checkState(!built, "A Procedure was already built.");
        }


        // params
        public LinkedHashMap<VarDecl<?>, Direction> getParams() {
            return params;
        }

        public void createParam(final Direction direction, final VarDecl<?> param) {
            checkNotBuilt();
            params.put(param, direction);
        }

        // localVars
        public Map<VarDecl<?>, Optional<LitExpr<?>>> getLocalVars() {
            return localVars;
        }

        public void createVar(final VarDecl<?> var, final LitExpr<?> initValue) {
            checkNotBuilt();
            localVars.put(var, Optional.ofNullable(initValue));
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

        public XcfaLocation addLoc(XcfaLocation loc) {
            checkNotBuilt();
            if(!locs.contains(loc))
                locs.add(loc);
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
            if(!edges.contains(e)) edges.add(e);
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
            this.errorLoc = errorLoc;
            errorLoc.setErrorLoc(true);
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

        public XcfaProcedure build() {
            checkState(initLoc != null, "Initial location must be set.");
            checkState(finalLoc != null, "Final location must be set.");
            checkState(finalLoc.getOutgoingEdges().isEmpty(), "Final location cannot have outgoing edges.");
            if (errorLoc != null)
                checkState(errorLoc.getOutgoingEdges().isEmpty(), "Error location cannot have outgoing edges.");
            Builder builder = XcfaPassManager.run(this);
            built = true;
            return new XcfaProcedure(builder);
        }

        public void removeEdge(XcfaEdge xcfaEdge) {
            edges.remove(xcfaEdge);
            xcfaEdge.getTarget().removeIncomingEdge(xcfaEdge);
            xcfaEdge.getSource().removeOutgoingEdge(xcfaEdge);
        }
    }

    public enum Direction{
        IN,
        OUT,
        INOUT
    }
}
