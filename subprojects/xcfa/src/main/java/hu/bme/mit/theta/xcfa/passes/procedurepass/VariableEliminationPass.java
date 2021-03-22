package hu.bme.mit.theta.xcfa.passes.procedurepass;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.*;
import hu.bme.mit.theta.core.stmt.xcfa.*;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.xcfa.dsl.CallStmt;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

import java.util.*;

import static com.google.common.base.Preconditions.checkState;

/*
 * This class provides a variable elimination pass.
 * It gets rid of redundant variables:
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

    private Set<VarDecl<?>> localVars;
    private Map<VarDecl<?>, Integer> lhsUse;
    private Map<VarDecl<?>, Map<XcfaEdge, Set<Stmt>>> lhsEdges;
    private Set<VarDecl<?>> noMove;

    @Override
    public XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {
        localVars = builder.getLocalVars().keySet();

        lhsUse = new HashMap<>();
        lhsEdges = new HashMap<>();
        noMove = new HashSet<>();

        for (XcfaEdge edge : builder.getEdges()) {
            for (Stmt stmt : edge.getStmts()) {
                stmt.accept(new MyStmtVisitor<>(), edge);
            }
        }

        lhsUse.forEach((varDecl, integer) -> {
            if (!noMove.contains(varDecl)) {
                lhsEdges.get(varDecl).forEach((xcfaEdge, stmts) -> {
                    List<Stmt> newStmts = new ArrayList<>(xcfaEdge.getStmts());
                    for (Stmt stmt : stmts) {
                        Stmt newStmt = stmt.accept(new RemoveLhsVisitor(), stmt);
                        int i = newStmts.indexOf(stmt);
                        newStmts.remove(i);
                        if(newStmt != null) newStmts.add(i, newStmt);
                    }
                    XcfaEdge newEdge = new XcfaEdge(xcfaEdge.getSource(), xcfaEdge.getTarget(), newStmts);
                    int i = builder.getEdges().indexOf(xcfaEdge);
                    builder.getEdges().remove(i);
                    builder.getEdges().add(i, newEdge);
                });
                builder.getLocalVars().remove(varDecl);
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
            List<VarDecl<?>> rhsVars = collectVars(stmt.getCond());
            for (VarDecl<?> rhsVar : rhsVars) {
                if (localVars.contains(rhsVar)) {
                    noMove.add(rhsVar);
                }
            }
            return null;
        }

        @Override
        public <DeclType extends Type> R visit(AssignStmt<DeclType> stmt, XcfaEdge edge) {
            VarDecl<?> lhs = stmt.getVarDecl();

            if (localVars.contains(lhs)) {
                if(!lhsEdges.containsKey(lhs)) lhsEdges.put(lhs, new HashMap<>());
                Set<Stmt> stmts = lhsEdges.get(lhs).getOrDefault(edge, new HashSet<>());
                stmts.add(stmt);
                lhsEdges.get(lhs).put(edge, stmts);
                lhsUse.put(lhs, lhsUse.getOrDefault(lhs, 0) + 1);
            }
            List<VarDecl<?>> rhsVars = collectVars(stmt.getExpr());
            for (VarDecl<?> rhsVar : rhsVars) {
                if (localVars.contains(rhsVar)) {
                    noMove.add(rhsVar);
                }
            }
            return null;
        }

        @Override
        public <DeclType extends Type> R visit(HavocStmt<DeclType> stmt, XcfaEdge edge) {
            VarDecl<?> lhs =  stmt.getVarDecl();
            if (localVars.contains(lhs)) {
                if(!lhsEdges.containsKey(lhs)) lhsEdges.put(lhs, new HashMap<>());
                Set<Stmt> stmts = lhsEdges.get(lhs).getOrDefault(edge, new HashSet<>());
                stmts.add(stmt);
                lhsEdges.get(lhs).put(edge, stmts);
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
            for (Expr<?> param : stmt.getParams()) {
                List<VarDecl<?>> rhsVars = collectVars(param);
                for (VarDecl<?> rhsVar : rhsVars) {
                    if (localVars.contains(rhsVar)) {
                        noMove.add(rhsVar);
                    }
                }
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

    private static class RemoveLhsVisitor implements XcfaStmtVisitor<Stmt, Stmt> {
        @Override
        public Stmt visit(SkipStmt stmt, Stmt param) {
            return null;
        }

        @Override
        public Stmt visit(AssumeStmt stmt, Stmt param) {
            return null;
        }

        @Override
        public <DeclType extends Type> Stmt visit(AssignStmt<DeclType> stmt, Stmt param) {
            return null;
        }

        @Override
        public <DeclType extends Type> Stmt visit(HavocStmt<DeclType> stmt, Stmt param) {
            return null;
        }

        @Override
        public Stmt visit(XcfaStmt xcfaStmt, Stmt param) {
            return null;
        }

        @Override
        public Stmt visit(SequenceStmt stmt, Stmt param) {
            return null;
        }

        @Override
        public Stmt visit(NonDetStmt stmt, Stmt param) {
            return null;
        }

        @Override
        public Stmt visit(OrtStmt stmt, Stmt param) {
            return null;
        }

        @Override
        public Stmt visit(XcfaCallStmt stmt, Stmt param) {
            XcfaProcedure proc = (XcfaProcedure) stmt.getProc();
            return new CallStmt(null, proc, stmt.getParams());
        }

        @Override
        public Stmt visit(StoreStmt storeStmt, Stmt param) {
            return null;
        }

        @Override
        public Stmt visit(LoadStmt loadStmt, Stmt param) {
            return null;
        }

        @Override
        public Stmt visit(FenceStmt fenceStmt, Stmt param) {
            return null;
        }

        @Override
        public Stmt visit(AtomicBeginStmt atomicBeginStmt, Stmt param) {
            return null;
        }

        @Override
        public Stmt visit(AtomicEndStmt atomicEndStmt, Stmt param) {
            return null;
        }

        @Override
        public Stmt visit(NotifyAllStmt notifyAllStmt, Stmt param) {
            return null;
        }

        @Override
        public Stmt visit(NotifyStmt notifyStmt, Stmt param) {
            return null;
        }

        @Override
        public Stmt visit(WaitStmt waitStmt, Stmt param) {
            return null;
        }

        @Override
        public Stmt visit(MtxLockStmt lockStmt, Stmt param) {
            return null;
        }

        @Override
        public Stmt visit(MtxUnlockStmt unlockStmt, Stmt param) {
            return null;
        }

        @Override
        public Stmt visit(ExitWaitStmt exitWaitStmt, Stmt param) {
            return null;
        }

        @Override
        public Stmt visit(EnterWaitStmt enterWaitStmt, Stmt param) {
            return null;
        }

        @Override
        public Stmt visit(XcfaInternalNotifyStmt enterWaitStmt, Stmt param) {
            return null;
        }
    }
}
