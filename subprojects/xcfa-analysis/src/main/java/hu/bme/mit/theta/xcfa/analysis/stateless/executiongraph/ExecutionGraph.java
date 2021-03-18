package hu.bme.mit.theta.xcfa.analysis.stateless.executiongraph;

import hu.bme.mit.theta.common.TupleN;
import hu.bme.mit.theta.common.datalog.DatalogArgument;
import hu.bme.mit.theta.common.datalog.StringDatalogArgument;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.xcfa.XCFAProcess;
import hu.bme.mit.theta.xcfa.XcfaState;
import hu.bme.mit.theta.xcfa.analysis.stateless.executiongraph.atoms.Thread;
import hu.bme.mit.theta.xcfa.analysis.stateless.executiongraph.atoms.Var;
import hu.bme.mit.theta.xcfa.analysis.stateless.executiongraph.atoms.Write;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

public class ExecutionGraph {
    private final ExecutionGraphDatabase executionGraphDatabase;
    private final Map<VarDecl<? extends Type>, Var> varLut;
    private final Map<XCFAProcess, Thread> threadLut;
    private final Thread initialThread;
    private final Set<Write> initialWrites;
    private final Map<XCFAProcess, DatalogArgument> lastNode;

    ExecutionGraph(XcfaState initialState) {
        this.executionGraphDatabase = ExecutionGraphDatabase.createExecutionGraph();
        this.varLut = new LinkedHashMap<>();
        this.threadLut = new LinkedHashMap<>();
        this.initialWrites = new LinkedHashSet<>();
        this.initialThread = new Thread();
        this.lastNode = new LinkedHashMap<>();
        for (VarDecl<? extends Type> globalVar : initialState.getXcfa().getGlobalVars()) {
            this.varLut.putIfAbsent(globalVar, new Var());
            addInitialWrite(new Write(initialState.getXcfa().getInitValue(globalVar)), this.varLut.get(globalVar));
        }
    }

    private void addInitialWrite(Write write, Var var) {
        initialWrites.add(write);
        executionGraphDatabase.getNodeLabels().addFact(TupleN.of(write, new StringDatalogArgument("w")));
        executionGraphDatabase.getThreadMapping().addFact(TupleN.of(write, initialThread));
        executionGraphDatabase.getVarMapping().addFact(TupleN.of(write, var));
    }

    public void addWrite(XCFAProcess process, VarDecl<? extends Type> varDecl, LitExpr<?> litExpr) {
        varLut.putIfAbsent(varDecl, new Var());
        Write write = new Write(litExpr);
        if(!threadLut.containsKey(process)) {
            threadLut.put(process, new Thread());
            for (Write initialWrite : initialWrites) {
                executionGraphDatabase.getEdgeLabels().addFact(TupleN.of(initialWrite, write, new StringDatalogArgument("po")));
            }
        } else {
            executionGraphDatabase.getEdgeLabels().addFact(TupleN.of(lastNode.get(process), write, new StringDatalogArgument("po")));
        }
        lastNode.put(process, write);
        executionGraphDatabase.getNodeLabels().addFact(TupleN.of(write, new StringDatalogArgument("W")));
        executionGraphDatabase.getThreadMapping().addFact(TupleN.of(write, threadLut.get(process)));
        executionGraphDatabase.getVarMapping().addFact(TupleN.of(write, varLut.get(varDecl)));

        //executionGraphDatabase.getRevisitables().getElements().stream().filter(objects -> objects.get(0));
    }


}
