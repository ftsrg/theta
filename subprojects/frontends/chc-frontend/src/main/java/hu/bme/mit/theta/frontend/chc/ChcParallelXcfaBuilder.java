/*
 *  Copyright 2026 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.frontend.chc;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Iff;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;
import static hu.bme.mit.theta.frontend.chc.ChcUtils.getTailConditionLabels;
import static hu.bme.mit.theta.frontend.chc.ChcUtils.resetSymbolTable;
import static hu.bme.mit.theta.frontend.chc.ChcUtils.transformConst;
import static hu.bme.mit.theta.frontend.chc.ChcUtils.transformSort;

import hu.bme.mit.theta.chc.frontend.dsl.gen.CHCParser;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.type.rattype.RatType;
import hu.bme.mit.theta.core.utils.BvUtils;
import hu.bme.mit.theta.xcfa.model.EmptyMetaData;
import hu.bme.mit.theta.xcfa.model.SequenceLabel;
import hu.bme.mit.theta.xcfa.model.StartLabel;
import hu.bme.mit.theta.xcfa.model.StmtLabel;
import hu.bme.mit.theta.xcfa.model.XcfaBuilder;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaGlobalVar;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder;
import hu.bme.mit.theta.xcfa.passes.ProcedurePassManager;
import java.math.BigInteger;
import java.util.*;

/**
 * Non-linear CHCs as k statically started worker threads. Worker w holds one derived fact in its
 * own globals (at_w: the predicate, P_w_i: the arguments). A clause is an edge of worker w that
 * carries one body atom itself and reads the others from the facts held by workers w+1, w+2, ...
 * (Sethi-Ullman order), so k = the Strahler bound of the derivations makes the error location
 * reachable iff false is derivable. Without a static bound (two body atoms from the head's own
 * recursive SCC) the encoding under-approximates and a safe result is marked unreliable.
 */
public class ChcParallelXcfaBuilder implements ChcXcfaBuilder {
    public static final String INCOMPLETE = "chcParallelIncomplete";
    public static final int DEFAULT_WORKERS = 3;

    private final ProcedurePassManager procedurePassManager;
    private final int requestedWorkers;

    private final Map<String, List<Type>> preds = new LinkedHashMap<>();
    private final Map<String, Integer> predIds = new HashMap<>();
    private final List<Clause> clauses = new ArrayList<>();

    public ChcParallelXcfaBuilder(
            final ProcedurePassManager procedurePassManager, final int requestedWorkers) {
        this.procedurePassManager = procedurePassManager;
        this.requestedWorkers = requestedWorkers;
    }

    private record Atom(String pred, List<String> args) {}

    private record Clause(
            List<CHCParser.Var_declContext> varDecls,
            List<Atom> body,
            Atom head, // null: query
            CHCParser.Chc_tailContext tail) {}

    @Override
    public XcfaBuilder buildXcfa(CHCParser parser) {
        CHCParser.BenchmarkContext benchmark = parser.benchmark();
        for (CHCParser.Fun_declContext decl : benchmark.fun_decl()) {
            String name = predName(decl.symbol().getText());
            List<Type> types = decl.sort().stream().map(ChcUtils::transformSort).toList();
            preds.put(name, types);
            predIds.put(name, predIds.size() + 1);
        }
        for (CHCParser.Chc_assertContext ctx : benchmark.chc_assert()) {
            if (ctx.u_predicate() != null) {
                clauses.add(
                        new Clause(
                                List.of(),
                                List.of(),
                                new Atom(predName(ctx.u_predicate().getText()), List.of()),
                                null));
            } else {
                CHCParser.Chc_tailContext tail = ctx.chc_tail();
                clauses.add(
                        new Clause(
                                ctx.var_decl(),
                                tail == null ? List.of() : atoms(tail.u_pred_atom()),
                                atom(ctx.chc_head().u_pred_atom()),
                                tail));
            }
        }
        CHCParser.Chc_queryContext query = benchmark.chc_query();
        clauses.add(
                new Clause(
                        query.var_decl(),
                        atoms(query.chc_tail().u_pred_atom()),
                        null,
                        query.chc_tail()));

        Analysis analysis = new Analysis();
        int workers =
                requestedWorkers > 0
                        ? requestedWorkers
                        : analysis.bounded ? analysis.queryCost() : DEFAULT_WORKERS;
        boolean incomplete = !analysis.bounded || workers < analysis.queryCost();

        XcfaBuilder xcfaBuilder = new XcfaBuilder("chc");
        if (incomplete) xcfaBuilder.getMetaData().put(INCOMPLETE, true);

        // globals: at_w and P_w_i per worker
        List<Map<String, List<VarDecl<?>>>> held = new ArrayList<>();
        List<VarDecl<IntType>> at = new ArrayList<>();
        for (int w = 1; w <= workers; w++) {
            VarDecl<IntType> atVar = Decls.Var("at_" + w, IntType.getInstance());
            xcfaBuilder.addVar(new XcfaGlobalVar(atVar, Int(0)));
            at.add(atVar);
            Map<String, List<VarDecl<?>>> vars = new LinkedHashMap<>();
            for (var pred : preds.entrySet()) {
                List<VarDecl<?>> args = new ArrayList<>();
                for (int i = 0; i < pred.getValue().size(); i++) {
                    VarDecl<?> v =
                            Decls.Var(pred.getKey() + "_" + w + "_" + i, pred.getValue().get(i));
                    xcfaBuilder.addVar(new XcfaGlobalVar(v, zero(v.getType())));
                    args.add(v);
                }
                vars.put(pred.getKey(), args);
            }
            held.add(vars);
        }

        // main: initialise the globals, start the workers
        XcfaProcedureBuilder main = new XcfaProcedureBuilder("main", procedurePassManager);
        main.createInitLoc();
        main.createFinalLoc();
        xcfaBuilder.addEntryPoint(main, new ArrayList<>());
        List<XcfaLabel> init = new ArrayList<>();
        for (int w = 0; w < workers; w++) {
            init.add(assign(at.get(w), Int(0)));
            for (List<VarDecl<?>> args : held.get(w).values())
                for (VarDecl<?> v : args) {
                    LitExpr<?> z = zero(v.getType());
                    if (z != null) init.add(assign(v, z));
                }
        }
        XcfaLocation from = main.getInitLoc();
        XcfaLocation to = newLoc(main, "main_init");
        main.addEdge(new XcfaEdge(from, to, new SequenceLabel(init), EmptyMetaData.INSTANCE));
        from = to;

        for (int w = 1; w <= workers; w++) {
            XcfaProcedureBuilder worker = buildWorker(w, workers, held, at, analysis);
            xcfaBuilder.addProcedure(worker);
            VarDecl<IntType> pid = Decls.Var("pid_" + w, IntType.getInstance());
            main.addVar(pid);
            to = w == workers ? main.getFinalLoc().get() : newLoc(main, "main_start_" + w);
            main.addEdge(
                    new XcfaEdge(
                            from,
                            to,
                            new StartLabel(
                                    worker.getName(),
                                    new ArrayList<>(),
                                    pid,
                                    EmptyMetaData.INSTANCE,
                                    Map.of()),
                            EmptyMetaData.INSTANCE));
            from = to;
        }
        return xcfaBuilder;
    }

    private XcfaProcedureBuilder buildWorker(
            int w,
            int workers,
            List<Map<String, List<VarDecl<?>>>> held,
            List<VarDecl<IntType>> at,
            Analysis analysis) {
        XcfaProcedureBuilder worker = new XcfaProcedureBuilder("worker_" + w, procedurePassManager);
        worker.createInitLoc();
        worker.createErrorLoc();
        XcfaLocation initLoc = worker.getInitLoc();
        Map<String, XcfaLocation> locs = new HashMap<>();
        for (String pred : preds.keySet()) locs.put(pred, newLoc(worker, "w" + w + "_" + pred));
        Map<String, List<VarDecl<?>>> own = held.get(w - 1);

        // drop the held fact
        for (String pred : preds.keySet()) {
            List<XcfaLabel> labels = new ArrayList<>(zeroAll(own.get(pred)));
            labels.add(assign(at.get(w - 1), Int(0)));
            worker.addEdge(
                    new XcfaEdge(
                            locs.get(pred),
                            initLoc,
                            new SequenceLabel(labels),
                            EmptyMetaData.INSTANCE));
        }

        Map<String, VarDecl<?>> locals = new HashMap<>();
        for (Clause clause : clauses) {
            List<Atom> order = analysis.order(clause);
            if (w + Math.max(order.size(), 1) - 1 > workers) continue;

            resetSymbolTable();
            Map<String, VarDecl<?>> vars = new HashMap<>();
            for (CHCParser.Var_declContext decl : clause.varDecls()) {
                String name = decl.symbol().getText();
                Type type = transformSort(decl.sort());
                VarDecl<?> v =
                        locals.computeIfAbsent(
                                name + ":" + type,
                                k -> {
                                    VarDecl<?> nv =
                                            Decls.Var(
                                                    "w" + w + "_" + name + "_" + locals.size(),
                                                    type);
                                    worker.addVar(nv);
                                    return nv;
                                });
                transformConst(Decls.Const(name, type), false);
                vars.put(name, v);
            }

            List<XcfaLabel> labels = new ArrayList<>();
            for (VarDecl<?> v : new LinkedHashSet<>(vars.values()))
                labels.add(new StmtLabel(HavocStmt.of(v)));
            Set<String> bound = new HashSet<>();
            for (int j = 0; j < order.size(); j++) {
                Atom a = order.get(j);
                List<VarDecl<?>> source = held.get(w - 1 + j).get(a.pred());
                if (j > 0)
                    labels.add(
                            new StmtLabel(
                                    AssumeStmt.of(
                                            AbstractExprs.Eq(
                                                    at.get(w - 1 + j).getRef(),
                                                    Int(predIds.get(a.pred()))))));
                for (int i = 0; i < a.args().size(); i++) {
                    VarDecl<?> local = vars.get(a.args().get(i));
                    labels.add(
                            bound.add(a.args().get(i))
                                    ? assign(local, source.get(i).getRef())
                                    : new StmtLabel(AssumeStmt.of(eq(local, source.get(i)))));
                }
            }
            if (clause.tail() != null) labels.addAll(getTailConditionLabels(clause.tail(), vars));
            String ownPred = order.isEmpty() ? null : order.get(0).pred();
            Atom head = clause.head();
            if (ownPred != null && (head == null || !ownPred.equals(head.pred())))
                labels.addAll(zeroAll(own.get(ownPred)));
            if (head != null) {
                for (int i = 0; i < head.args().size(); i++)
                    labels.add(
                            assign(
                                    own.get(head.pred()).get(i),
                                    vars.get(head.args().get(i)).getRef()));
                if (!head.pred().equals(ownPred))
                    labels.add(assign(at.get(w - 1), Int(predIds.get(head.pred()))));
            } else {
                labels.add(assign(at.get(w - 1), Int(0)));
            }
            labels.addAll(zeroAll(new ArrayList<>(new LinkedHashSet<>(vars.values()))));

            XcfaLocation source = ownPred == null ? initLoc : locs.get(ownPred);
            XcfaLocation target = head == null ? worker.getErrorLoc().get() : locs.get(head.pred());
            worker.addEdge(
                    new XcfaEdge(
                            source, target, new SequenceLabel(labels), EmptyMetaData.INSTANCE));
        }
        return worker;
    }

    /** SCCs of the predicate dependency graph and the worker bound of each clause. */
    private class Analysis {
        final Map<String, Integer> comp = new HashMap<>();
        final Map<Integer, Integer> need = new HashMap<>();
        boolean bounded = true;

        Analysis() {
            Map<String, Set<String>> succ = new HashMap<>();
            for (Clause c : clauses)
                if (c.head() != null)
                    for (Atom a : c.body())
                        succ.computeIfAbsent(a.pred(), k -> new LinkedHashSet<>())
                                .add(c.head().pred());
            tarjan(succ);
            for (Clause c : clauses)
                if (c.head() != null) {
                    int s = comp.get(c.head().pred());
                    if (c.body().stream().filter(a -> comp.get(a.pred()) == s).count() >= 2)
                        bounded = false;
                }
            // condensation in topological order: Tarjan emits SCCs in reverse topological order
            List<Integer> topo = new ArrayList<>(new LinkedHashSet<>(sccOrder));
            Collections.reverse(topo);
            for (int s : topo) {
                int best = 1;
                for (Clause c : clauses)
                    if (c.head() != null && comp.get(c.head().pred()) == s)
                        best = Math.max(best, cost(c));
                need.put(s, best);
            }
        }

        int queryCost() {
            int best = 1;
            for (Clause c : clauses) if (c.head() == null) best = Math.max(best, cost(c));
            return best;
        }

        private int needOf(Atom a, Integer headComp) {
            if (headComp != null && comp.get(a.pred()).equals(headComp))
                return DEFAULT_WORKERS; // second own-SCC atom: unbounded, any order
            return need.getOrDefault(comp.get(a.pred()), 1);
        }

        /** Own atom first (the one in the head's SCC, else the most expensive), then the rest. */
        List<Atom> order(Clause c) {
            Integer headComp = c.head() == null ? null : comp.get(c.head().pred());
            List<Atom> rest = new ArrayList<>(c.body());
            Atom own = null;
            if (headComp != null)
                for (Atom a : rest)
                    if (comp.get(a.pred()).equals(headComp)) {
                        own = a;
                        break;
                    }
            if (own != null) rest.remove(own);
            rest.sort(Comparator.comparingInt((Atom a) -> -needOf(a, headComp)));
            if (own == null && !rest.isEmpty()) own = rest.remove(0);
            List<Atom> out = new ArrayList<>();
            if (own != null) out.add(own);
            out.addAll(rest);
            return out;
        }

        int cost(Clause c) {
            Integer headComp = c.head() == null ? null : comp.get(c.head().pred());
            List<Atom> order = order(c);
            boolean ownInScc =
                    !order.isEmpty()
                            && headComp != null
                            && comp.get(order.get(0).pred()).equals(headComp);
            int k = 1;
            for (int j = 0; j < order.size(); j++) {
                if (j == 0 && ownInScc) continue;
                k = Math.max(k, needOf(order.get(j), headComp) + j);
            }
            return Math.max(k, order.size());
        }

        private final List<Integer> sccOrder = new ArrayList<>();

        private void tarjan(Map<String, Set<String>> succ) {
            Map<String, Integer> index = new HashMap<>(), low = new HashMap<>();
            Deque<String> stack = new ArrayDeque<>();
            Set<String> onStack = new HashSet<>();
            int[] counter = {0};
            for (String root : preds.keySet()) {
                if (index.containsKey(root)) continue;
                Deque<Map.Entry<String, Iterator<String>>> work = new ArrayDeque<>();
                index.put(root, counter[0]);
                low.put(root, counter[0]++);
                stack.push(root);
                onStack.add(root);
                work.push(Map.entry(root, succ.getOrDefault(root, Set.of()).iterator()));
                while (!work.isEmpty()) {
                    var top = work.peek();
                    String u = top.getKey();
                    if (top.getValue().hasNext()) {
                        String v = top.getValue().next();
                        if (!index.containsKey(v)) {
                            index.put(v, counter[0]);
                            low.put(v, counter[0]++);
                            stack.push(v);
                            onStack.add(v);
                            work.push(Map.entry(v, succ.getOrDefault(v, Set.of()).iterator()));
                        } else if (onStack.contains(v)) {
                            low.put(u, Math.min(low.get(u), index.get(v)));
                        }
                    } else {
                        work.pop();
                        if (!work.isEmpty()) {
                            String parent = work.peek().getKey();
                            low.put(parent, Math.min(low.get(parent), low.get(u)));
                        }
                        if (low.get(u).equals(index.get(u))) {
                            int id = index.get(u);
                            String v;
                            do {
                                v = stack.pop();
                                onStack.remove(v);
                                comp.put(v, id);
                            } while (!v.equals(u));
                            sccOrder.add(id);
                        }
                    }
                }
            }
        }
    }

    private static String predName(String text) {
        return text.replace("|", "");
    }

    private static Atom atom(CHCParser.U_pred_atomContext ctx) {
        return new Atom(
                predName(ctx.u_predicate().getText()),
                ctx.symbol().stream().map(s -> s.getText()).toList());
    }

    private static List<Atom> atoms(List<CHCParser.U_pred_atomContext> ctxs) {
        return ctxs == null ? List.of() : ctxs.stream().map(ChcParallelXcfaBuilder::atom).toList();
    }

    private static XcfaLocation newLoc(XcfaProcedureBuilder builder, String name) {
        XcfaLocation loc = new XcfaLocation(name, EmptyMetaData.INSTANCE);
        builder.addLoc(loc);
        return loc;
    }

    private static StmtLabel assign(VarDecl<?> v, Expr<?> value) {
        return new StmtLabel(AssignStmt.create(v, value));
    }

    @SuppressWarnings("unchecked")
    private static Expr<BoolType> eq(VarDecl<?> a, VarDecl<?> b) {
        if (a.getType() instanceof BoolType)
            return Iff((Expr<BoolType>) a.getRef(), (Expr<BoolType>) b.getRef());
        return (Expr<BoolType>) (Expr<?>) AbstractExprs.Eq(a.getRef(), b.getRef());
    }

    private static List<XcfaLabel> zeroAll(List<VarDecl<?>> vars) {
        List<XcfaLabel> labels = new ArrayList<>();
        for (VarDecl<?> v : vars) {
            LitExpr<?> z = zero(v.getType());
            if (z != null) labels.add(assign(v, z));
        }
        return labels;
    }

    private static LitExpr<?> zero(Type type) {
        if (type instanceof IntType) return Int(0);
        if (type instanceof RatType) return Rat(0, 1);
        if (type instanceof BoolType) return False();
        if (type instanceof BvType bv)
            return BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.ZERO, bv.getSize());
        return null;
    }
}
