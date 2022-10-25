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

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.rattype.RatType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.StmtUtils;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public final class XtaProcess {
    private final String name;
    private final XtaSystem system;
    private final Collection<Loc> locs;
    private final Collection<Edge> edges;
    private Loc initLoc;

    private final Collection<Loc> unmodLocs;
    private final Collection<Edge> unmodEdges;

    private final HashMap<Loc, HashSet<VarDecl<RatType>>> activeClockMap;

    ////

    private XtaProcess(final XtaSystem system, final String name) {
        this.system = checkNotNull(system);
        this.name = checkNotNull(name);
        locs = Containers.createSet();
        edges = new ArrayList<>();

        unmodLocs = Collections.unmodifiableCollection(locs);
        unmodEdges = Collections.unmodifiableCollection(edges);
        activeClockMap = new HashMap<Loc, HashSet<VarDecl<RatType>>>();
    }
    public HashMap<Loc, HashSet<VarDecl<RatType>>> getActiveClockMap(){
        return activeClockMap;
    }

    static XtaProcess create(final XtaSystem system, final String name) {
        return new XtaProcess(system, name);
    }

    ////

    public String getName() {
        return name;
    }

    public XtaSystem getSystem() {
        return system;
    }

    public Collection<Loc> getLocs() {
        return unmodLocs;
    }

    public Collection<Edge> getEdges() {
        return unmodEdges;
    }

    public Loc getInitLoc() {
        checkNotNull(initLoc);
        return initLoc;
    }

    ////

    public void setInitLoc(final Loc loc) {
        checkNotNull(loc);
        checkArgument(locs.contains(loc));
        this.initLoc = loc;
    }

    public Loc createLoc(final String name, final LocKind kind, final Collection<Expr<BoolType>> invars) {
        final Loc loc = new Loc(name, kind, invars);
        locs.add(loc);
        return loc;
    }

    public Edge createEdge(final Loc source, final Loc target, final Collection<Expr<BoolType>> guards,
                           final Optional<Sync> sync, final List<Stmt> updates) {
        checkArgument(locs.contains(source));
        checkArgument(locs.contains(target));
        if(!name.equals("ErrorProc") && !target.getKind().equals(LocKind.ERROR)) {
            int count = 0;
            for (VarDecl<?> var : system.getDataVars()) {
                if (!target.equals(source) || count == 2) {
                    if (var.getName().contains(target.name)) {
                        updates.add(AssignStmt.create(var, BoolLitExpr.of(true)));
                        count++;
                    }
                    if (var.getName().contains(source.name)) {
                        updates.add(AssignStmt.create(var, BoolLitExpr.of(false)));
                        count++;
                    }
                } else break;
            }
        }
        final Edge edge = new Edge(source, target, guards, sync, updates);
        source.outEdges.add(edge);
        target.inEdges.add(edge);

        return edge;
    }

    ////

    private Collection<Guard> createGuards(final Collection<Expr<BoolType>> exprs) {
        checkNotNull(exprs);

        final ImmutableList.Builder<Guard> builder = ImmutableList.builder();
        for (final Expr<BoolType> expr : exprs) {
            final Collection<VarDecl<?>> vars = ExprUtils.getVars(expr);

            boolean dataExpr = false;
            boolean clockExpr = false;
            for (final VarDecl<?> varDecl : vars) {
                if (system.getDataVars().contains(varDecl)) {
                    dataExpr = true;
                } else if (system.getClockVars().contains(varDecl)) {
                    clockExpr = true;
                } else {
                    throw new IllegalArgumentException("Undeclared variable: " + varDecl.getName());
                }
            }

            final Guard guard;
            if (dataExpr && !clockExpr) {
                guard = Guard.dataGuard(expr);
            } else if (!dataExpr && clockExpr) {
                guard = Guard.clockGuard(expr);
            } else {
                throw new UnsupportedOperationException();
            }
            builder.add(guard);
        }
        return builder.build();
    }

    private List<Update> createUpdates(final List<Stmt> stmts) {
        checkNotNull(stmts);

        final ImmutableList.Builder<Update> builder = ImmutableList.builder();
        for (final Stmt stmt : stmts) {
            final Collection<VarDecl<?>> varsDecls = StmtUtils.getVars(stmt);
            boolean dataStmt = false;
            boolean clockStmt = false;
            for (final VarDecl<?> varDecl : varsDecls) {
                if (system.getDataVars().contains(varDecl)) {
                    dataStmt = true;
                } else if (system.getClockVars().contains(varDecl)) {
                    clockStmt = true;
                } else {
                    throw new IllegalArgumentException("Undeclared variable: " + varDecl.getName());
                }
            }

            final Update update;
            if (dataStmt && !clockStmt) {
                update = Update.dataUpdate(stmt);
            } else if (!dataStmt && clockStmt) {
                update = Update.clockUpdate(stmt);
            } else {
                throw new UnsupportedOperationException();
            }
            builder.add(update);
        }
        return builder.build();
    }

    public void createActiveClockMap(){
        //1st iter
        for(Loc l: locs){
            HashSet<VarDecl<RatType>> clocks = new HashSet<VarDecl<RatType>>();
            List<Collection<VarDecl<RatType>>> temp = l.getInvars().stream().map(invar -> invar.asClockGuard().getClockConstr().getVars()).collect(Collectors.toList());
            if(!temp.isEmpty())
                for(Collection<VarDecl<RatType>> t: temp) clocks.addAll(t);
            temp.clear();
            for(Edge e: l.outEdges){
                temp = e.getGuards().stream().filter(g ->g.isClockGuard()).map(g -> g.asClockGuard().getClockConstr().getVars()).collect(Collectors.toList());
                if(!temp.isEmpty())
                    for(Collection<VarDecl<RatType>> t: temp) clocks.addAll(t);
                temp.clear();
            }
            activeClockMap.put(l, clocks);
        }
        boolean done = false;

        while(!done){
            HashMap<Loc, HashSet<VarDecl<RatType>>> old_activeClockMap =  new HashMap<Loc, HashSet<VarDecl<RatType>>>();
            for(Loc l: locs){
                HashSet<VarDecl<RatType>> old_val = new HashSet<VarDecl<RatType>>(activeClockMap.get(l));
                old_activeClockMap.put(l, old_val);
                for (Edge e: l.outEdges){
                    activeClockMap.get(l).addAll(activeClockMap.get(e.target));
                    List<Collection<VarDecl<RatType>>>  temp = e.updates.stream().filter(u -> u.isClockUpdate()).map(u -> u.asClockUpdate().getClockOp().getVars()).collect(Collectors.toList());
                    ArrayList<VarDecl<RatType>> temp1 = new ArrayList<VarDecl<RatType>>();
                    for(Collection<VarDecl<RatType>> t: temp) temp1.addAll(t);
                    for(VarDecl<RatType> t: temp1){
                        if(activeClockMap.get(l).contains(t))
                            activeClockMap.get(l).remove(t);
                    }
                }

            }
            if (activeClockMap.equals(old_activeClockMap)) done = true;
        }
    }

    ////

    public enum LocKind {
        NORMAL, URGENT, COMMITTED, ERROR;
    }

    public final class Loc {
        private final Collection<Edge> inEdges;
        private final Collection<Edge> outEdges;
        private final String name;
        private final LocKind kind;
        private final Collection<Guard> invars;

        private final Collection<Edge> unmodInEdges;
        private final Collection<Edge> unmodOutEdges;

        private Loc(final String name, final LocKind kind, final Collection<Expr<BoolType>> invars) {
            inEdges = new ArrayList<>();
            outEdges = new ArrayList<>();
            this.name = checkNotNull(name);
            this.kind = checkNotNull(kind);
            this.invars = createGuards(invars);

            unmodInEdges = Collections.unmodifiableCollection(inEdges);
            unmodOutEdges = Collections.unmodifiableCollection(outEdges);
        }

        public Collection<Edge> getInEdges() {
            return unmodInEdges;
        }

        public Collection<Edge> getOutEdges() {
            return unmodOutEdges;
        }

        public String getName() {
            return name;
        }

        public LocKind getKind() {
            return kind;
        }

        public Collection<Guard> getInvars() {
            return invars;
        }

        @Override
        public String toString() {
            return Utils.lispStringBuilder("loc").add(name).toString();
        }
    }

    ////

    public final class Edge {
        private final Loc source;
        private final Loc target;
        private final Collection<Guard> guards;
        private final Optional<Sync> sync;
        private final List<Update> updates;

        private Edge(final Loc source, final Loc target, final Collection<Expr<BoolType>> guards,
                     final Optional<Sync> sync, final List<Stmt> updates) {
            this.source = checkNotNull(source);
            this.target = checkNotNull(target);
            this.guards = createGuards(guards);
            this.sync = checkNotNull(sync);
            this.updates = createUpdates(updates);
        }

        public Loc getSource() {
            return source;
        }

        public Loc getTarget() {
            return target;
        }

        public Collection<Guard> getGuards() {
            return guards;
        }

        public Optional<Sync> getSync() {
            return sync;
        }

        public List<Update> getUpdates() {
            return updates;
        }
    }



}
