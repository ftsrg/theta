package hu.bme.mit.theta.xcfa;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;

import java.util.*;

import static com.google.common.base.Preconditions.*;

public final class XcfaProcedure {
    private XcfaProcess parent;
    private final String name;
    private final Type rtype;
    private final VarDecl<? extends Type> result;

    private final List<VarDecl<?>> params;

    private final Map<VarDecl<?>, Optional<LitExpr<?>>> localVars;

    private final List<Location> locs;
    private final Location initLoc;
    private final Location errorLoc;
    private final Location finalLoc;

    private final List<Edge> edges;

    private XcfaProcedure(final Builder builder) {
        rtype = builder.rtype;
        params = ImmutableList.copyOf(builder.params);
        localVars = builder.localVars;
        locs = ImmutableList.copyOf(builder.locs);
        locs.forEach(location -> location.parent = this);
        initLoc = builder.initLoc;
        errorLoc = builder.errorLoc;
        finalLoc = builder.finalLoc;
        edges = ImmutableList.copyOf(builder.edges);
        edges.forEach(edge -> edge.parent = this);
        result = builder.result;
        name = builder.name;
    }

    public XcfaProcedure(XcfaProcedure procedure) {
        parent = null; // ProcessBuilder will fill out this field
        rtype = procedure.rtype;

        List<VarDecl<?>> paramCollectList = new ArrayList<>();
        procedure.params.forEach(varDecl -> paramCollectList.add(VarDecl.copyOf(varDecl)));
        params = ImmutableList.copyOf(paramCollectList);

        Map<VarDecl<?>, Optional<LitExpr<?>>> localVarsCollectList = new HashMap<>();
        procedure.localVars.forEach((varDecl, litExpr) -> localVarsCollectList.put(VarDecl.copyOf(varDecl), litExpr));
        localVars = ImmutableMap.copyOf(localVarsCollectList);

        Map<Location, Location> newLocLut = new HashMap<>();

        List<Location> locsCollectList = new ArrayList<>();
        procedure.locs.forEach(loc -> {
            Location location = Location.copyOf(loc);
            locsCollectList.add(location);
            newLocLut.put(loc, location);
        });
        locs = ImmutableList.copyOf(locsCollectList);
        locs.forEach(location -> location.parent = this);

        initLoc = newLocLut.get(procedure.initLoc);
        errorLoc = newLocLut.get(procedure.errorLoc);
        finalLoc = newLocLut.get(procedure.finalLoc);

        List<Edge> edgeCollectList = new ArrayList<>();
        procedure.edges.forEach(edge -> edgeCollectList.add(Edge.copyOf(edge, newLocLut)));
        edges = ImmutableList.copyOf(edgeCollectList);
        edges.forEach(edge -> edge.parent = this);

        result = procedure.result == null ? null : VarDecl.copyOf(procedure.result);
        name = procedure.name;
    }

    public static Builder builder() {
        return new Builder();
    }

    public String toDot() {
        StringBuilder ret = new StringBuilder();
        for (Location location : getLocs()) {
            ret.append("\"").append(location.getName()).append("\"");
            if (location.isErrorLoc()) ret.append("[xlabel=err]");
            else if (location.isEndLoc()) ret.append("[xlabel=final]");
            else if (getInitLoc() == location) ret.append("[xlabel=start]");
            ret.append(";\n");
        }
        for (Edge edge : getEdges()) {
            ret.append("\"").append(edge.getSource().getName()).append("\" -> ");
            ret.append("\"").append(edge.getTarget().getName()).append("\" [label=\"");
            for (Stmt stmt : edge.getStmts()) {
                ret.append(stmt.toString());
                ret.append(", ");
            }
            ret.append("\"];\n");
        }
        return ret.toString();
    }

    public Type getRtype() {
        return rtype;
    }

    public List<VarDecl<?>> getParams() {
        return params;
    }

    public List<VarDecl<?>> getLocalVars() {
        return List.copyOf(localVars.keySet());
    }

    public Optional<LitExpr<?>> getInitValue(VarDecl<?> varDecl) {
        return localVars.get(varDecl);
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

    public XcfaProcess getParent() {
        return parent;
    }

    public void setParent(XcfaProcess xcfaProcess) {
        this.parent = xcfaProcess;
    }

    public static final class Location {
        private XcfaProcedure parent;
        private final String name;
        private boolean isErrorLoc = false;
        private boolean isEndLoc = false;

        private final Map<String, String> dictionary;

        private final List<Edge> incomingEdges;
        private final List<Edge> outgoingEdges;

        public Location(final String name, final Map<String, String> dictionary) {
            this.name = checkNotNull(name);
            this.dictionary = dictionary;
            outgoingEdges = new ArrayList<>();
            incomingEdges = new ArrayList<>();
        }

        public static Location copyOf(final Location from) {
            return new Location(from.getName(), Map.copyOf(from.dictionary));
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

        public boolean isErrorLoc() {
            return isErrorLoc;
        }

        public void setErrorLoc(boolean errorLoc) {
            isErrorLoc = errorLoc;
        }

        public boolean isEndLoc() {
            return isEndLoc;
        }

        public void setEndLoc(boolean endLoc) {
            isEndLoc = endLoc;
        }

        public XcfaProcedure getParent() {
            return parent;
        }
    }

    public static final class Edge {
        private XcfaProcedure parent;
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

        public static Edge copyOf(Edge edge, Map<Location, Location> locationLut) {
            return new Edge(locationLut.get(edge.source), locationLut.get(edge.target), edge.stmts);
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

        public XcfaProcedure getParent() {
            return parent;
        }
    }

    public static final class Builder {
        private static final String RESULT_NAME = "result";
        private final List<VarDecl<?>> params;
        private final Map<VarDecl<?>, Optional<LitExpr<?>>> localVars;
        private final List<Location> locs;
        private final List<Edge> edges;
        private boolean built;
        private String name;
        private Type rtype;
        private VarDecl<?> result;
        private Location initLoc;
        private Location errorLoc;
        private Location finalLoc;

        private Builder() {
            params = new ArrayList<>();
            localVars = new HashMap<>();
            locs = new ArrayList<>();
            edges = new ArrayList<>();
            built = false;
        }

        public void createParam(final VarDecl<?> param) {
            checkNotBuilt();
            params.add(param);
        }

        public void createVar(final VarDecl<?> var, final LitExpr<?> initValue) {
            checkNotBuilt();
            localVars.put(var, Optional.ofNullable(initValue));
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

        public Map<VarDecl<?>, Optional<LitExpr<?>>> getLocalVars() {
            return localVars;
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
            checkArgument(!initLoc.equals(errorLoc), "Init location cannot be the same as error location.");
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
            errorLoc.setErrorLoc(true);
        }

        public Location getFinalLoc() {
            return finalLoc;
        }

        public void setFinalLoc(final Location finalLoc) {
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
            checkState(finalLoc.outgoingEdges.isEmpty(), "Final location cannot have outgoing edges.");
            if (errorLoc != null)
                checkState(errorLoc.outgoingEdges.isEmpty(), "Error location cannot have outgoing edges.");
            built = true;
            return new XcfaProcedure(this);
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
