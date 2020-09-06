package hu.bme.mit.theta.xcfa.analysis.stateless;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.model.MutablePartitionedValuation;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.xcfa.XCFA;

import java.util.*;

public class State {

    private final MutablePartitionedValuation mutableValuation;
    private final Map<XCFA.Process, Integer> partitionLUT; 
    private final XCFA xcfa;
    private final Map<XCFA.Process, List<Tuple2<XCFA.Process.Procedure, XCFA.Process.Procedure.Location>>> callStacks;
    private final Map<XCFA.Process, XCFA.Process.Procedure.Location> currentLocs;
    private XCFA.Process currentlyAtomic;

    public State(final XCFA xcfa) {
        this.mutableValuation = new MutablePartitionedValuation();
        this.xcfa = xcfa;
        this.callStacks = new HashMap<>();
        this.currentLocs = new HashMap<>();
        for(XCFA.Process process : xcfa.getProcesses()) {
            this.callStacks.put(process, new ArrayList<>());
            this.currentLocs.put(process, process.getMainProcedure().getInitLoc());
        }
        currentlyAtomic = null;
        mutableValuation.createPartition();
        partitionLUT = new HashMap<>();
    }

    private State(
            final MutablePartitionedValuation mutableValuation,
            final XCFA xcfa,
            final Map<XCFA.Process, List<Tuple2<XCFA.Process.Procedure, XCFA.Process.Procedure.Location>>> callStacks,
            Map<XCFA.Process, Integer> partitionLUT, final Map<XCFA.Process, XCFA.Process.Procedure.Location> currentLocs,
            final XCFA.Process currentlyAtomic
    ) {
        this.mutableValuation = MutablePartitionedValuation.copyOf(mutableValuation);
        this.xcfa = xcfa;
        this.partitionLUT = new HashMap<>(partitionLUT);
        this.callStacks = new HashMap<>();
        for(XCFA.Process process : xcfa.getProcesses()) {
            this.callStacks.put(process, new ArrayList<>(callStacks.get(process)));
        }
        this.currentLocs =  new HashMap<>(currentLocs);
        this.currentlyAtomic = currentlyAtomic;
    }

    public static State copyOf(State state) {
        return new State(state.mutableValuation, state.xcfa, state.callStacks, state.partitionLUT, state.currentLocs, state.currentlyAtomic);
    }

    public MutablePartitionedValuation getMutablePartitionedValuation() {
        return mutableValuation;
    }

    public XCFA getXcfa() {
        return xcfa;
    }

    public Map<XCFA.Process, List<Tuple2<XCFA.Process.Procedure, XCFA.Process.Procedure.Location>>> getCallStacks() {
        return callStacks;
    }

    public Map<XCFA.Process, XCFA.Process.Procedure.Location> getCurrentLocs() {
        return currentLocs;
    }

    public XCFA.Process getCurrentlyAtomic() {
        return currentlyAtomic;
    }

    public void setCurrentlyAtomic(XCFA.Process currentlyAtomic) {
        this.currentlyAtomic = currentlyAtomic;
    }

    public Tuple2<XCFA.Process, XCFA.Process.Procedure.Edge> getOneStep() {
        for(XCFA.Process process : currentlyAtomic == null ? xcfa.getProcesses() : Collections.singleton(currentlyAtomic)) {
            for(XCFA.Process.Procedure.Edge edge : currentLocs.get(process).getOutgoingEdges()) {
                boolean disabled = false;
                for(Stmt stmt : edge.getStmts()) {
                    if(stmt instanceof AssumeStmt) {
                        if(((BoolLitExpr)((AssumeStmt) stmt).getCond().eval(mutableValuation)).getValue()) {
                            return Tuple2.of(process, edge);
                        }
                        else {
                            disabled = true;
                            break;
                        }
                    }
                }
                if(!disabled) {
                    return Tuple2.of(process, edge);
                }
            }
        }
        return null;
    }

    public int getPartitionId(XCFA.Process proc) {
        if(!partitionLUT.containsKey(proc)) {
            partitionLUT.put(proc, mutableValuation.createPartition());
        }
        return partitionLUT.get(proc);
    }
}
