package hu.bme.mit.theta.xcfa.ir.handlers.states;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.Tuple3;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.xcfa.dsl.CallStmt;
import hu.bme.mit.theta.xcfa.ir.SSAProvider;
import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.model.XcfaProcess;

import java.util.*;

import static hu.bme.mit.theta.xcfa.ir.Utils.*;

public class GlobalState {
    private int globalCounter = 0;
    private final XCFA.Builder builder;
    private final Map<String, VarDecl<?>> globalVars;
    private final Map<String, XcfaProcess.Builder> processes;
    private final List<Tuple3<String, Optional<String>, List<Tuple2<String, String>>>> procedures;
    private final Map<CallStmt, String> callStmts;
    private final SSAProvider ssa;

    public GlobalState(SSAProvider ssa) {
        this.ssa = ssa;
        builder = XCFA.builder();
        this.globalVars = new HashMap<>();
        this.callStmts = new HashMap<>();
        this.processes = new HashMap<>();
        this.procedures = new ArrayList<>();

        // Creating global variables
        for (Tuple3<String, String, String> globalVariable : ssa.getGlobalVariables()) {
            try {
                VarDecl<?> variable = createVariable(globalVariable.get1(), globalVariable.get2());
                globalVars.put(globalVariable.get1(), variable);
                builder.getGlobalVars().put(variable, Optional.of(createConstant(globalVariable.get3())));
            } catch(RuntimeException re) {
                re.printStackTrace();
            }
        }

        XcfaProcess.Builder mainProcBuilder = XcfaProcess.builder();
        mainProcBuilder.setName("main");
        processes.put(mainProcBuilder.getName(), mainProcBuilder);

    }

    public void finalizeGlobalState(BuiltState builtState) {
        callStmts.forEach((callStmt, s) -> callStmt.setProcedure(builtState.getProcedures().getOrDefault(s, createEmptyProc(s))));
    }

    public Map<String, VarDecl<?>> getGlobalVars() {
        return globalVars;
    }

    public void addGlobalVar(String name, VarDecl<?> globalVar) {
        this.globalVars.put(name, globalVar);
    }

    public Map<String, XcfaProcess.Builder> getProcesses() {
        return processes;
    }

    public void addProcess(String name, XcfaProcess.Builder process) {
        this.processes.put(name, process);
    }

    public int getGlobalCounter() {
        int cnt = globalCounter;
        ++globalCounter;
        return cnt;
    }

    public List<Tuple3<String, Optional<String>, List<Tuple2<String, String>>>> getProcedures() {
        return procedures;
    }

    public void addProcedure(Tuple3<String, Optional<String>, List<Tuple2<String, String>>> proc) {
        procedures.add(proc);
    }

    public SSAProvider getProvider() {
        return ssa;
    }

    public XCFA.Builder getBuilder() {
        return builder;
    }

    public Map<CallStmt, String> getCallStmts() {
        return callStmts;
    }
}
