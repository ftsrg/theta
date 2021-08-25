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

import hu.bme.mit.theta.common.Tuple3;
import hu.bme.mit.theta.common.Tuple4;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.MutablePartitionedValuation;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.stmt.xcfa.JoinThreadStmt;
import hu.bme.mit.theta.core.stmt.xcfa.StartThreadStmt;
import hu.bme.mit.theta.core.stmt.xcfa.XcfaCallStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverStatus;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.Stack;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neg;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

/*
 * This class is used to represent the state of an XCFA program. The following primitives are supported:
 *      - processes
 *      - procedures
 *      - AtomicBegin, AtomicEnd
 *      - StartThread, JoinThread
 */
public class XcfaState {

    private final XCFA xcfa;

    private final List<XcfaProcess> enabledProcesses;
    private final Map<VarDecl<?>, Decl<?>> lastInstance;
    private final Map<XcfaProcess, Solver> solvers;
    private final Map<XcfaProcess, Stack<XcfaStackFrame>> stackFrames;
    private final Map<XcfaProcess, Set<XcfaStackFrame>> offers;
    private XcfaProcess currentlyAtomic;

    //private final Collection<Consumer<XcfaProcess>> newProcessListeners;

    XcfaState(XCFA xcfa) {
        this.xcfa = xcfa;
        enabledProcesses = new ArrayList<>();
        solvers = new LinkedHashMap<>();
        stackFrames = new LinkedHashMap<>();
        offers = new LinkedHashMap<>();
        currentlyAtomic = null;
        if(xcfa.isDynamic()) {
            addNewEnabledProcess(xcfa.getMainProcess());
        } else {
            for (XcfaProcess process : xcfa.getProcesses()) {
                addNewEnabledProcess(process);
            }
        }
        recalcOffers();
        lastInstance = new LinkedHashMap<>();
    }

    public Decl<?> getNewInstance(VarDecl<?> varDecl) {
        Decl<?> ret = Const(varDecl.getName(), varDecl.getType());
        lastInstance.put(varDecl,ret);
        return ret;
    }

    public Expr<?> getInstantiatedExpression(Expr<?> expr) {
        Set<VarDecl<?>> vars = ExprUtils.getVars(expr);
        for (VarDecl<?> var : vars) {
            getNewInstance(var);
        }
        return XcfaStmtVarReplacer.replaceVars(expr, lastInstance);
    }

    public Map<XcfaProcess, Solver> getSolvers() {
        return solvers;
    }

    public List<XcfaProcess> getEnabledProcesses() {
        return enabledProcesses;
    }

    public void addNewEnabledProcess(XcfaProcess process) {
        enabledProcesses.add(process);
        stackFrames.put(process, new Stack<>());
        solvers.put(process, Z3SolverFactory.getInstance().createSolver());
        offers.put(process, new LinkedHashSet<>());
    }

    public Map<XcfaProcess, Stack<XcfaStackFrame>> getStackFrames() {
        return stackFrames;
    }

    public XcfaProcess getCurrentlyAtomic() {
        return currentlyAtomic;
    }

    public void setCurrentlyAtomic(XcfaProcess currentlyAtomic) {
        checkState(currentlyAtomic == null || enabledProcesses.contains(currentlyAtomic), "The atomic process is not enabled!");
        this.currentlyAtomic = currentlyAtomic;
    }

    public XCFA getXcfa() {
        return xcfa;
    }

    public Map<XcfaProcess, Set<XcfaStackFrame>> getOffers() {
        return offers;
    }

    private final Map<VarDecl<?>, XcfaProcess> ids = new LinkedHashMap<>();
    private final Map<XcfaProcess, XcfaProcess> waiting = new LinkedHashMap<>();

    void acceptOffer(XcfaStackFrame frame) {
        XcfaProcess proc = frame.getProcess();
        checkState(offers.getOrDefault(proc, new HashSet<>()).contains(frame), "Stack frame is not currently offered!");
        XcfaStackFrame lastFrame = null;
        if (!stackFrames.get(proc).empty()) {
            lastFrame = stackFrames.get(proc).pop();
        }
        if (frame.isLastStmt() && frame.getEdge().getTarget().isEndLoc() && (!(frame.getStmt() instanceof XcfaCallStmt) || frame.isHandled()) && !stackFrames.get(proc).empty()) {
            returnFromProcedure(frame, proc);
        }

        if(frame.getStmt() instanceof StartThreadStmt) {
            checkState(xcfa.isDynamic(), "Only dynamic XCFAs shall have thread start statements!");
            VarDecl<?> key = ((StartThreadStmt) frame.getStmt()).getKey(); // TODO: param
            XcfaProcess process = new XcfaProcess(frame.getEdge(), (StartThreadStmt) frame.getStmt(), xcfa.getMainProcess());
            ids.put(key, process);
            addNewEnabledProcess(process);
        }

        if(frame.getStmt() instanceof JoinThreadStmt) {
            checkState(ids.get(((JoinThreadStmt) frame.getStmt()).getKey()) != null, "Thread to be joined has not yet started!");
            waiting.put(frame.getProcess(), ids.get(((JoinThreadStmt) frame.getStmt()).getKey()));
            enabledProcesses.remove(frame.getProcess());
        }

        if (frame.isNewProcedure() && lastFrame != null) {
            stackFrames.get(proc).push(lastFrame);
        }

        if (!(frame.isLastStmt() && frame.getEdge().getTarget().isEndLoc() && (!(frame.getStmt() instanceof XcfaCallStmt) || frame.isHandled()))) {
            stackFrames.get(proc).push(frame);
        } else if (stackFrames.get(proc).empty()) {
            enabledProcesses.remove(proc);
        }

        recalcOffers();
    }

    private void returnFromProcedure(XcfaStackFrame frame, XcfaProcess proc) {
        XcfaStackFrame beforeFrame =  stackFrames.get(proc).peek();
        Stmt stmt = beforeFrame.getStmt();
        checkState(stmt instanceof XcfaCallStmt, "New stack frame can only originate from an XcfaCallStmt!");
        int cnt = 0;
        Optional<XcfaProcedure> first = proc.getProcedures().stream().filter(procedure -> procedure.getName().equals(((XcfaCallStmt) stmt).getProcedure())).findFirst();
        checkState(first.isPresent(), "No such procedure!");
        XcfaProcedure procedure = first.get();
        for (Map.Entry<VarDecl<?>, XcfaProcedure.Direction> e : procedure.getParams().entrySet()) {
            VarDecl<?> var = e.getKey();
            XcfaProcedure.Direction direction = e.getValue();
            if(direction != XcfaProcedure.Direction.IN) {
                Expr<?> expr = ((XcfaCallStmt) stmt).getParams().get(cnt);
                checkState(expr instanceof RefExpr<?>, "OUT/INOUT params must be variables!");
                solvers.get(proc).add(Eq(getNewInstance(var).getRef(), getInstantiatedExpression(expr)));
            }
            ++cnt;
        }
    }

    private void recalcOffers() {
        offers.forEach((process, xcfaStackFrames) -> xcfaStackFrames.clear());
        if (currentlyAtomic != null) {
            collectOffers(currentlyAtomic);
        } else {
            for (XcfaProcess enabledProcess : enabledProcesses) {
                collectOffers(enabledProcess);
            }
        }

    }

    private void collectOffers(XcfaProcess enabledProcess) {
        XcfaStackFrame last = stackFrames.get(enabledProcess).empty() ? null : stackFrames.get(enabledProcess).peek();
        if(last != null && last.isLastStmt() && (!(last.getStmt() instanceof XcfaCallStmt) || last.isHandled()) && last.getEdge().getTarget().isEndLoc()) {
            XcfaStackFrame pop = stackFrames.get(enabledProcess).pop();
            returnFromProcedure(pop, enabledProcess);
            collectOffers(enabledProcess);
        } else if (last != null && last.getStmt() instanceof XcfaCallStmt && !last.isHandled()) {
            XcfaProcedure procedure = enabledProcess.getProcedures().stream().filter(xcfaProcedure -> xcfaProcedure.getName().equals(((XcfaCallStmt) last.getStmt()).getProcedure())).findFirst().orElse(null);
            checkState(procedure != null, "Procedure should not be null! Unknown procedure name?");
            int i = 0;
            for (Map.Entry<VarDecl<?>, XcfaProcedure.Direction> entry : procedure.getParams().entrySet()) {
                VarDecl<?> key = entry.getKey();
                XcfaProcedure.Direction direction = entry.getValue();
                if(direction != XcfaProcedure.Direction.OUT) {
                    Expr<?> expr = ((XcfaCallStmt) last.getStmt()).getParams().get(i);
                    solvers.get(enabledProcess).add(Eq(getNewInstance(key).getRef(), getInstantiatedExpression(expr)));
                }
                ++i;
            }
            last.setHandled(true);
            collectProcedureOffers(enabledProcess, procedure);
        } else if (last == null || last.isLastStmt()) {
            XcfaLocation sourceLoc = last == null ? enabledProcess.getMainProcedure().getInitLoc() : last.getEdge().getTarget();
            for (XcfaEdge outgoingEdge : sourceLoc.getOutgoingEdges()) {
                boolean canExecute = true;
                for (Stmt stmt : outgoingEdge.getStmts()) {
                    if (stmt instanceof AssumeStmt) {
                        solvers.get(enabledProcess).push();
                        solvers.get(enabledProcess).add(cast(getInstantiatedExpression(((AssumeStmt) stmt).getCond()), Bool()));
                        if(solvers.get(enabledProcess).check() == SolverStatus.UNSAT) canExecute = false;
                        solvers.get(enabledProcess).pop();
                        break;
                    }
                }
                if (!canExecute) continue;
                XcfaStackFrame xcfaStackFrame = new XcfaStackFrame(this, outgoingEdge, outgoingEdge.getStmts().get(0));
                if (outgoingEdge.getStmts().size() == 1) xcfaStackFrame.setLastStmt();
                offers.get(enabledProcess).add(xcfaStackFrame);

            }
        } else {
            int i = last.getEdge().getStmts().indexOf(last.getStmt()) + 1;
            Stmt stmt = last.getEdge().getStmts().get(i);
            XcfaStackFrame xcfaStackFrame = last.duplicate(this);
            xcfaStackFrame.setStmt(stmt);
            if (last.getEdge().getStmts().size() == i + 1) xcfaStackFrame.setLastStmt();
            offers.get(enabledProcess).add(xcfaStackFrame);
        }
    }

    private void collectProcedureOffers(XcfaProcess enabledProcess, XcfaProcedure procedure) {
        for (XcfaEdge edge : procedure.getInitLoc().getOutgoingEdges()) {
            boolean canExecute = true;
            for (Stmt stmt : edge.getStmts()) {
                if (stmt instanceof AssumeStmt) {
                    solvers.get(enabledProcess).push();
                    solvers.get(enabledProcess).add(cast(getInstantiatedExpression(((AssumeStmt) stmt).getCond()), Bool()));
                    if(solvers.get(enabledProcess).check() == SolverStatus.UNSAT) canExecute = false;
                    solvers.get(enabledProcess).pop();
                    break;
                }
            }
            if (!canExecute) continue;

            XcfaStackFrame xcfaStackFrame = new XcfaStackFrame(this, edge, edge.getStmts().get(0));
            if (edge.getStmts().size() == 1) xcfaStackFrame.setLastStmt();
            xcfaStackFrame.setNewProcedure();
            offers.get(enabledProcess).add(xcfaStackFrame);
        }
    }

    public Optional<? extends LitExpr<?>> lookup(VarDecl<?> varDecl) {
        if(lastInstance.get(varDecl) == null) return Optional.empty();
        for (XcfaProcess process : solvers.keySet()) {
            try {
                Optional<? extends LitExpr<?>> eval = solvers.get(process).getModel().eval(lastInstance.get(varDecl));
                if (eval.isPresent()) return eval;
            } catch (IllegalStateException exception) {
                // NOP
            }
        }
        return Optional.empty();
    }

    private final Map<XcfaStackFrame, Tuple3<Map<VarDecl<?>, Decl<?>>, Collection<Expr<BoolType>>, Stack<XcfaStackFrame>>> resetPoints = new LinkedHashMap<>();

    public void addResetPoint(XcfaStackFrame frame) {
        XcfaProcess proc = frame.getProcess();
        Stack<XcfaStackFrame> copy = new Stack<>();
        for (XcfaStackFrame xcfaStackFrame : stackFrames.get(proc)) {
            copy.push(xcfaStackFrame.duplicate(this));
        }
        resetPoints.put(frame, Tuple3.of(
                new LinkedHashMap<>(lastInstance.entrySet().stream().filter(varDeclDeclEntry -> proc.getProcedures().stream().anyMatch(xcfaProcedure -> xcfaProcedure.getLocalVars().contains(varDeclDeclEntry.getKey()))).collect(Collectors.toMap(o -> o.getKey(), o -> o.getValue()))),
                solvers.get(proc).getAssertions(),
                copy));
    }

    public void rollback(XcfaStackFrame frame) {
        checkState(resetPoints.containsKey(frame), "No reset point exists for the provided frame!");
        XcfaProcess proc = frame.getProcess();
        stackFrames.put(proc, resetPoints.get(frame).get3());
        solvers.put(proc, Z3SolverFactory.getInstance().createSolver());
        solvers.get(proc).add(resetPoints.get(frame).get2());
        resetPoints.get(frame).get1().forEach(lastInstance::put);
    }
}
