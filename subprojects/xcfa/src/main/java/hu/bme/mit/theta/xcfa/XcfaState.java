package hu.bme.mit.theta.xcfa;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.MutablePartitionedValuation;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.stmt.xcfa.XcfaCallStmt;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;

import java.util.*;

import static com.google.common.base.Preconditions.checkState;

/*
 * This class is used to represent the state of an XCFA program. Currently the following primitives are supported:
 *      - processes
 *      - procedures
 *      - AtomicBegin, AtomicEnd
 *      - Assignments
 * The following are *not* supported:
 *      - Mutex
 *      - CndSync
 */
public class XcfaState {

    private final XCFA xcfa;

    private final List<XCFA.Process> enabledProcesses;
    private final MutablePartitionedValuation valuation;
    private final Map<XCFA.Process, Stack<XcfaStackFrame>> stackFrames;
    private final Map<XCFA.Process, Integer> partitions;
    private XCFA.Process currentlyAtomic;

    private final Map<XCFA.Process, Set<XcfaStackFrame>> offers;

    XcfaState(XCFA xcfa) {
        this.xcfa = xcfa;
        enabledProcesses = new ArrayList<>(xcfa.getProcesses());
        valuation = new MutablePartitionedValuation();
        stackFrames = new LinkedHashMap<>();
        partitions = new LinkedHashMap<>();
        offers = new LinkedHashMap<>();
        enabledProcesses.forEach(process -> {
            stackFrames.put(process, new Stack<>());
            partitions.put(process, valuation.createPartition());
            offers.put(process, new LinkedHashSet<>());
        });
        currentlyAtomic = null;
        recalcOffers();
    }

    public List<XCFA.Process> getEnabledProcesses() {
        return enabledProcesses;
    }

    public Map<XCFA.Process, Integer> getPartitions() {
        return partitions;
    }

    public Map<XCFA.Process, Stack<XcfaStackFrame>> getStackFrames() {
        return stackFrames;
    }

    public MutablePartitionedValuation getValuation() {
        return valuation;
    }

    public XCFA.Process getCurrentlyAtomic() {
        return currentlyAtomic;
    }

    public XCFA getXcfa() {
        return xcfa;
    }

    public Map<XCFA.Process, Set<XcfaStackFrame>> getOffers() {
        return offers;
    }

    public void setCurrentlyAtomic(XCFA.Process currentlyAtomic) {
        checkState(enabledProcesses.contains(currentlyAtomic), "The atomic process is not enabled!");
        this.currentlyAtomic = currentlyAtomic;
    }

    public void addValuation(int id, VarDecl<?> decl, LitExpr<?> value) {
        valuation.put(id, decl, value);
    }

    public Optional<? extends LitExpr<?>> eval(VarDecl<?> decl) {
        return valuation.eval(decl);
    }

    public void setEnabledProcesses(Collection<XCFA.Process> processes) {
        enabledProcesses.clear();
        enabledProcesses.addAll(processes);
    }

    void acceptOffer(XcfaStackFrame frame) {
        XCFA.Process proc = frame.getProcess();
        checkState(offers.getOrDefault(proc, new HashSet<>()).contains(frame), "Stack frame is not currently offered!");
        if(! (frame.getStmt() instanceof XcfaCallStmt) && !stackFrames.get(proc).empty()) {
            stackFrames.get(proc).pop();
        }

        if(!frame.isLastStmt() || frame.getEdge().getParent().getFinalLoc() != frame.getEdge().getTarget()) {
            stackFrames.get(proc).push(frame);
        }
        else {
            if(stackFrames.get(proc).empty()) enabledProcesses.remove(proc);
        }

        recalcOffers();
    }

    public boolean test(Map<VarDecl<?>, LitExpr<?>> expected) {
        for (Map.Entry<VarDecl<?>, LitExpr<?>> entry : expected.entrySet()) {
            VarDecl<?> varDecl = entry.getKey();
            LitExpr<?> litExpr = entry.getValue();
            Optional<? extends LitExpr<?>> eval = valuation.eval(varDecl);
            if(eval.isEmpty() || !eval.get().equals(litExpr)) return false;
        }
        return true;
    }

    private void recalcOffers() {
        offers.forEach((process, xcfaStackFrames) -> xcfaStackFrames.clear());
        if(currentlyAtomic != null) {
            collectOffers(currentlyAtomic);
        }
        else {
            for (XCFA.Process enabledProcess : enabledProcesses) {
                collectOffers(enabledProcess);
            }
        }

    }

    private void collectOffers(XCFA.Process enabledProcess) {
        XcfaStackFrame last = stackFrames.get(enabledProcess).empty() ? null : stackFrames.get(enabledProcess).peek();
        if(last == null || last.isLastStmt()) {
            XCFA.Process.Procedure.Location sourceLoc = last == null ? enabledProcess.getMainProcedure().getInitLoc() : last.getEdge().getTarget();
            for (XCFA.Process.Procedure.Edge outgoingEdge : sourceLoc.getOutgoingEdges()) {
                boolean canExecute = true;
                for (Stmt stmt : outgoingEdge.getStmts()) {
                    if(stmt instanceof AssumeStmt) {
                        canExecute = ((BoolLitExpr) ((AssumeStmt) stmt).getCond().eval(valuation)).getValue();
                        break;
                    }
                }
                XcfaStackFrame xcfaStackFrame = new XcfaStackFrame(this, outgoingEdge, outgoingEdge.getStmts().get(0));
                if(outgoingEdge.getStmts().size() == 1) xcfaStackFrame.setLastStmt();
                if(canExecute) offers.get(enabledProcess).add(xcfaStackFrame);
            }
        }
        else {
            XcfaStackFrame xcfaStackFrame = last.duplicate(this);
            int i = last.getEdge().getStmts().indexOf(last.getStmt()) + 1;
            xcfaStackFrame.setStmt(last.getEdge().getStmts().get(i));
            if(last.getEdge().getStmts().size() == i+1) xcfaStackFrame.setLastStmt();
            offers.get(enabledProcess).add(xcfaStackFrame);
        }
    }
}
