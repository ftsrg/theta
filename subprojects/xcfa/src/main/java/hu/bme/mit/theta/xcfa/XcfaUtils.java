package hu.bme.mit.theta.xcfa;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.Tuple3;
import hu.bme.mit.theta.common.Tuple4;
import hu.bme.mit.theta.xcfa.dsl.CallStmt;
import hu.bme.mit.theta.xcfa.dsl.XcfaDslManager;
import hu.bme.mit.theta.xcfa.ir.handlers.Instruction;
import hu.bme.mit.theta.xcfa.ir.handlers.InstructionHandler;
import hu.bme.mit.theta.xcfa.ir.handlers.InstructionHandlerManager;
import hu.bme.mit.theta.xcfa.ir.handlers.states.BlockState;
import hu.bme.mit.theta.xcfa.ir.handlers.states.BuiltState;
import hu.bme.mit.theta.xcfa.ir.handlers.states.FunctionState;
import hu.bme.mit.theta.xcfa.ir.handlers.states.GlobalState;
import hu.bme.mit.theta.xcfa.ir.LlvmIrProvider;
import hu.bme.mit.theta.xcfa.ir.SSAProvider;
import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.model.XcfaProcess;
import hu.bme.mit.theta.xcfa.passes.procedurepass.ProcedurePass;
import hu.bme.mit.theta.xcfa.passes.procedurepass.VariableEliminationPass;
import hu.bme.mit.theta.xcfa.passes.processpass.ProcessPass;
import hu.bme.mit.theta.xcfa.passes.xcfapass.XcfaPass;

import java.io.*;
import java.util.*;

@SuppressWarnings("unused")
public class XcfaUtils {
    /*
     * Creates an XCFA from the specified file.
     * This is the recommended method for getting an XCFA instance.
     * Supports .xcfa, .ll, .bc, .c and .i files.
     */
    public static XCFA fromFile(File model) throws IOException {

        if (!model.exists()) throw new FileNotFoundException();

        if (model.getName().endsWith(".xcfa")) {
            try (InputStream is = new FileInputStream(model)) {
                return createXCFA(is);
            }

        } else if (model.getName().endsWith(".ll") || model.getName().endsWith(".bc")) {
            return createXCFA(new LlvmIrProvider(model.getAbsolutePath()));

        } else if (model.getName().endsWith(".c") || model.getName().endsWith(".i")) {
            return createXCFA(new LlvmIrProvider(model.getAbsolutePath(), false, true));

        } else {
            String[] split = model.getName().split("\\.");
            if (split.length > 0)
                throw new RuntimeException("File type " + split[split.length - 1] + " not supported.");
            throw new RuntimeException("File does not have an extension.");

        }
    }

    /*
     * Creates an XCFA from the provided InputStream using the XCFA DSL.
     */
    public static XCFA createXCFA(InputStream dsl) throws IOException {
        return XcfaDslManager.createXcfa(dsl);
    }

    /*
     * Creates an XCFA from the provided String using the XCFA DSL
     */
    public static XCFA createXCFA(String dsl) throws IOException {
        return XcfaDslManager.createXcfa(dsl);
    }


    /*
     * Creates an XCFA from the provided SSAProvider using its getter methods.
     */
    public static XCFA createXCFA(SSAProvider ssa) {
        return createXCFA(ssa, List.of(), List.of(), List.of(/*VariableEliminationPass.getInstance()*/));
    }

    /*
     * Creates an XCFA from the provided SSAProvider using its getter methods.
     * Runs the specified passes when a specific stage is complete.
     */
    public static XCFA createXCFA(SSAProvider ssa, List<XcfaPass> xcfaPasses, List<ProcessPass> processPasses, List<ProcedurePass> procedurePasses) {
        BuiltState builtState = new BuiltState();
        GlobalState globalState = new GlobalState(ssa);

        for (Tuple3<String, Optional<String>, List<Tuple2<String, String>>> function : ssa.getFunctions()) {
            FunctionState functionState = new FunctionState(globalState, function);

            for (String block : ssa.getBlocks(function.get1())) {
                BlockState blockState = new BlockState(functionState, block);
                InstructionHandlerManager instructionHandlerManager = new InstructionHandlerManager();
                for (Tuple4<String, Optional<Tuple2<String, String>>, List<Tuple2<Optional<String>, String>>, Integer> instruction : ssa.getInstructions(block)) {
                    try {
                        InstructionHandler instructionHandler = instructionHandlerManager.createInstructionHandlers();
                        instructionHandler.handleInstruction(new Instruction(instruction), globalState, functionState, blockState);
                    } catch (ReflectiveOperationException e) {
                        e.printStackTrace();
                    }

                }
            }

            functionState.finalizeFunctionState(builtState);

            for (ProcedurePass procedurePass : procedurePasses) {
                procedurePass.run(functionState.getProcedureBuilder());
            }

            builtState.getProcedures().put(function.get1(), functionState.getProcedureBuilder().build());
        }

        globalState.getProcesses().forEach((s, builder) -> {
            Map<CallStmt, CallStmt> newCallStmts = new HashMap<>();
            builtState.getProcedures().forEach((s1, xcfaProcedure) -> {
                XcfaProcedure procedure = new XcfaProcedure(xcfaProcedure, newCallStmts);
                builder.addProcedure(procedure);
                if(procedure.getName().equals("main")) builder.setMainProcedure(procedure);
            });
            newCallStmts.forEach((callStmt, callStmt2) -> globalState.getCallStmts().put(callStmt2, globalState.getCallStmts().get(callStmt)));
            XcfaProcess built = builder.build();
            builtState.getProcesses().put(s, built);
            globalState.getBuilder().addProcess(built);
        });

        globalState.finalizeGlobalState(builtState);
        globalState.getBuilder().setMainProcess(builtState.getProcesses().get("main"));
        return globalState.getBuilder().build();
    }
}
