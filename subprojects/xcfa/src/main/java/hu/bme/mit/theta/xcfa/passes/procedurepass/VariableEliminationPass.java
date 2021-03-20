package hu.bme.mit.theta.xcfa.passes.procedurepass;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.*;
import hu.bme.mit.theta.core.stmt.xcfa.*;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

import java.util.*;

import static com.google.common.base.Preconditions.checkState;

/*
 * This class provides a variable elimination pass.
 * It gets rid of two types of redundant variables:
 *  -   Variables that are assigned exactly once and then exclusively used (read) without a branch in-between
 *      - Exception: procedure calls, due to potential side effects
 *  -   Variables that are assigned exactly once and then never used (read).
 *      - Exception: return variable
 */
public class VariableEliminationPass implements ProcedurePass {

    private static final VariableEliminationPass instance = new VariableEliminationPass();

    private VariableEliminationPass(){}

    public static VariableEliminationPass getInstance() {
        return instance;
    }

    private static List<VarDecl<?>> collectVars(Expr<?> expr) {
        if (expr instanceof LitExpr<?>) return List.of();
        else if (expr instanceof RefExpr<?>) {
            Decl<?> decl = ((RefExpr<?>) expr).getDecl();
            if (decl instanceof VarDecl) return List.of((VarDecl<?>) decl);
            else return List.of();
        }
        else {
            List<VarDecl<?>> ret = new ArrayList<>();
            for (Expr<?> op : expr.getOps()) {
                ret.addAll(collectVars(op));
            }
            return ret;
        }
    }

    private static Set<XcfaEdge> collectDeterministicEdges(XcfaEdge xcfaEdge) {
        XcfaLocation loc = xcfaEdge.getTarget();
        Set<XcfaEdge> edges = new HashSet<>();
        edges.add(xcfaEdge);
        while(loc.getOutgoingEdges().size() == 1) {
            XcfaEdge edge = loc.getOutgoingEdges().get(0);
            loc = edge.getTarget();
            edges.add(edge);
        }
        return edges;
    }

    private Set<VarDecl<?>> localVars;
    private Map<VarDecl<?>, Integer> rhsUse;
    private Map<VarDecl<?>, Integer> lhsUse;
    private Map<VarDecl<?>, Set<XcfaEdge>> lhsEdges;
    private Map<VarDecl<?>, Set<XcfaEdge>> rhsEdges;
    private Set<VarDecl<?>> noMove;

    @Override
    public XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {
        localVars = builder.getLocalVars().keySet();

        rhsUse = new HashMap<>();
        lhsUse = new HashMap<>();
        lhsEdges = new HashMap<>();
        rhsEdges = new HashMap<>();
        noMove = new HashSet<>();

        for (XcfaEdge edge : builder.getEdges()) {
            for (Stmt stmt : edge.getStmts()) {
                stmt.accept(new MyStmtVisitor<>(), edge);
            }
        }

        lhsUse.forEach((varDecl, integer) -> {
            if (!noMove.contains(varDecl)) {
                Set<XcfaEdge> deterministicEdges = null;
                for (XcfaEdge xcfaEdge : lhsEdges.get(varDecl)) {
                    if(deterministicEdges == null) deterministicEdges = collectDeterministicEdges(xcfaEdge);
                    else deterministicEdges.retainAll(collectDeterministicEdges(xcfaEdge));
                }
                if (deterministicEdges != null && deterministicEdges.containsAll(lhsEdges.get(varDecl)) && (!rhsEdges.containsKey(varDecl) || deterministicEdges.containsAll(rhsEdges.get(varDecl)))){
                    // TODO: do actual removal
                    System.out.println(varDecl + " can be removed!");
                }
            }
        });

        return builder;
    }

    private class MyStmtVisitor<R>  implements XcfaStmtVisitor<XcfaEdge, R> {

        @Override
        public R visit(SkipStmt stmt, XcfaEdge edge) {
            return null;
        }

        @Override
        public R visit(AssumeStmt stmt, XcfaEdge edge) {
            return null;
        }

        @Override
        public <DeclType extends Type> R visit(AssignStmt<DeclType> stmt, XcfaEdge edge) {
            VarDecl<?> lhs = stmt.getVarDecl();
            List<VarDecl<?>> rhsVars = collectVars(stmt.getExpr());
            if (localVars.contains(lhs)) {
                if(!lhsEdges.containsKey(lhs)) lhsEdges.put(lhs, new HashSet<>());
                lhsEdges.get(lhs).add(edge);
                lhsUse.put(lhs, lhsUse.getOrDefault(lhs, 0) + 1);
            }
            for (VarDecl<?> rhsVar : rhsVars) {
                if (localVars.contains(rhsVar)) {
                    if(!rhsEdges.containsKey(lhs)) rhsEdges.put(rhsVar, new HashSet<>());
                    rhsEdges.get(rhsVar).add(edge);
                    rhsUse.put(rhsVar, rhsUse.getOrDefault(rhsVar, 0) + 1);
                }
            }
            return null;
        }

        @Override
        public <DeclType extends Type> R visit(HavocStmt<DeclType> stmt, XcfaEdge edge) {
            VarDecl<?> lhs =  stmt.getVarDecl();
            if (localVars.contains(lhs)) {
                if(!lhsEdges.containsKey(lhs)) lhsEdges.put(lhs, new HashSet<>());
                lhsEdges.get(lhs).add(edge);
                lhsUse.put(lhs, lhsUse.getOrDefault(lhs, 0) + 1);
            }
            return null;
        }

        @Override
        public R visit(XcfaStmt xcfaStmt, XcfaEdge edge) {
            return xcfaStmt.accept(this, edge);
        }

        @Override
        public R visit(SequenceStmt stmt, XcfaEdge edge) {
            return null;
        }

        @Override
        public R visit(NonDetStmt stmt, XcfaEdge edge) {
            return null;
        }

        @Override
        public R visit(OrtStmt stmt, XcfaEdge edge) {
            return null;
        }

        @Override
        public R visit(XcfaCallStmt stmt, XcfaEdge edge) {
            VarDecl<?> lhs =  stmt.getResultVar();
            if (localVars.contains(lhs)) {
                noMove.add(lhs);
            }
            return null;
        }

        @Override
        public R visit(StoreStmt storeStmt, XcfaEdge edge) {
            VarDecl<?> rhs =  storeStmt.getRhs();
            VarDecl<?> lhs =  storeStmt.getRhs();
            if (localVars.contains(lhs)) {
                noMove.add(lhs);
            }
            if (localVars.contains(rhs)) {
                noMove.add(rhs);
            }
            return null;
        }

        @Override
        public R visit(LoadStmt loadStmt, XcfaEdge edge) {
            VarDecl<?> lhs =  loadStmt.getLhs();
            VarDecl<?> rhs =  loadStmt.getRhs();
            if (localVars.contains(lhs)) {
                noMove.add(lhs);
            }
            if (localVars.contains(rhs)) {
                noMove.add(rhs);
            }
            return null;
        }

        @Override
        public R visit(FenceStmt fenceStmt, XcfaEdge edge) {
            return null;
        }

        @Override
        public R visit(AtomicBeginStmt atomicBeginStmt, XcfaEdge edge) {
            return null;
        }

        @Override
        public R visit(AtomicEndStmt atomicEndStmt, XcfaEdge edge) {
            return null;
        }

        @Override
        public R visit(NotifyAllStmt notifyAllStmt, XcfaEdge edge) {
            return null;
        }

        @Override
        public R visit(NotifyStmt notifyStmt, XcfaEdge edge) {
            return null;
        }

        @Override
        public R visit(WaitStmt waitStmt, XcfaEdge edge) {
            return null;
        }

        @Override
        public R visit(MtxLockStmt lockStmt, XcfaEdge edge) {
            return null;
        }

        @Override
        public R visit(MtxUnlockStmt unlockStmt, XcfaEdge edge) {
            return null;
        }

        @Override
        public R visit(ExitWaitStmt exitWaitStmt, XcfaEdge edge) {
            return null;
        }

        @Override
        public R visit(EnterWaitStmt enterWaitStmt, XcfaEdge edge) {
            return null;
        }

        @Override
        public R visit(XcfaInternalNotifyStmt enterWaitStmt, XcfaEdge edge) {
            return null;
        }
    }
}
