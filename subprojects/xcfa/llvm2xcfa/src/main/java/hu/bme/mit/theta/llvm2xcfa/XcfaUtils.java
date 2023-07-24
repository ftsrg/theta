/*
 *  Copyright 2023 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.llvm2xcfa;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.Tuple3;
import hu.bme.mit.theta.common.Tuple4;
import hu.bme.mit.theta.llvm2xcfa.handlers.Instruction;
import hu.bme.mit.theta.llvm2xcfa.handlers.InstructionHandler;
import hu.bme.mit.theta.llvm2xcfa.handlers.InstructionHandlerManager;
import hu.bme.mit.theta.llvm2xcfa.handlers.states.BlockState;
import hu.bme.mit.theta.llvm2xcfa.handlers.states.BuiltState;
import hu.bme.mit.theta.llvm2xcfa.handlers.states.FunctionState;
import hu.bme.mit.theta.llvm2xcfa.handlers.states.GlobalState;
import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.passes.ProcedurePass;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.List;
import java.util.Optional;

import static com.google.common.base.Preconditions.checkState;

@SuppressWarnings("unused")
public class XcfaUtils {
    /*
     * Creates an XCFA from the specified file.
     * This is the recommended method for getting an XCFA instance.
     * Supports .ll, .bc, .c and .i files.
     */
    public static XCFA fromFile(File model, ArithmeticType arithmeticType) throws IOException {

        if (!model.exists()) throw new FileNotFoundException();

        if (model.getName().endsWith("ll") || model.getName().endsWith("bc")) {
            return createXCFA(new LlvmIrProvider(model.getAbsolutePath()), arithmeticType);

        } else if (model.getName().endsWith("c") || model.getName().endsWith("i")) {
            return createXCFA(new LlvmIrProvider(model.getAbsolutePath(), true, true, true, true), arithmeticType);

        } else {
            String[] split = model.getName().split("\\.");
            if (split.length > 0)
                throw new RuntimeException("File type " + split[split.length - 1] + " not supported.");
            throw new RuntimeException("File does not have an extension.");

        }
    }

    /*
     * Creates an XCFA from the provided SSAProvider using its getter methods.
     */
    public static XCFA createXCFA(SSAProvider ssa, ArithmeticType arithmeticType) {
        return createXCFA(ssa, List.of(), arithmeticType);
    }

    /*
     * Creates an XCFA from the provided SSAProvider using its getter methods.
     * Runs the specified passes when a specific stage is complete.
     */
    public static XCFA createXCFA(SSAProvider ssa, List<ProcedurePass> procedurePasses, ArithmeticType arithmeticType) {
        if (ssa.hasStructs()) {
            throw new UnsupportedOperationException("Structs are not yet supported!");
        }

        if (arithmeticType == ArithmeticType.efficient && ssa.shouldUseBitwiseArithmetics()) {
            System.out.println("Using bitvector arithmetic!");
            arithmeticType = ArithmeticType.bitvector;
        } else if (arithmeticType == ArithmeticType.efficient) {
            System.out.println("Using integer arithmetic!");
            arithmeticType = ArithmeticType.integer;
        }
        checkState(!ssa.shouldUseBitwiseArithmetics() || arithmeticType == ArithmeticType.bitvector, "There are statements in the source not mappable to integer arithmetic");
        Utils.arithmeticType = arithmeticType;
        BuiltState builtState = new BuiltState();
        GlobalState globalState = new GlobalState(ssa, arithmeticType);

        for (Tuple3<String, Optional<String>, List<Tuple2<String, String>>> function : ssa.getFunctions()) {
            if (function.get1().equals("reach_error")) continue;
            FunctionState functionState = new FunctionState(globalState, function);

            for (String block : ssa.getBlocks(function.get1())) {
                BlockState blockState = new BlockState(functionState, block);
                InstructionHandlerManager instructionHandlerManager = new InstructionHandlerManager(arithmeticType);
                for (Tuple4<String, Optional<Tuple2<String, String>>, List<Tuple2<Optional<String>, String>>, Integer> instruction : ssa.getInstructions(function.get1(), block)) {
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

            builtState.getProcedures().put(function.get1(), functionState.getProcedureBuilder());

        }
        return globalState.getBuilder().build();
    }
//
//        if(builtState.getProcedures().size() > 1) {
//            System.err.println("Inlining failed.");
//            System.exit(-80);
//        }
//
//        builtState.getProcedures().forEach((s, builder) -> {
//            if(builder.getErrorLoc() == null) {
//                System.err.println("Frontend failed");
//                System.exit(-80);
//            }
//        });
//
//        final XCFA.Builder builder = globalState.getBuilder();
//
//        return new XCFA(builder.getGlobalVars(),
//                        List.of(
//                                xcfa -> new XcfaProcess("proc",
//                                                        List.of(),
//                                                        Map.of(),
//                                                        builtState.getProcedures().entrySet().stream().map(e ->
//                                                                (Function<XcfaProcess, XcfaProcedure>)
//                                                                (XcfaProcess xcfaProc) -> new XcfaProcedure(
//                                                                        e.getKey(),
//                                                                        Map.of(),
//                                                                        e.getValue().getLocalVars(),
//                                                                        e.getValue().getLocs(),
//                                                                        e.getValue().getRetType(),
//                                                                        e.getValue().getInitLoc(),
//                                                                        e.getValue().getErrorLoc(),
//                                                                        e.getValue().getFinalLoc(),
//                                                                        e.getValue().getEdges(),
//                                                                        xcfaProc)
//                                                            ).collect(Collectors.toList()),
//                                                        xcfa)),
//                        "xcfa",
//                        true);
}
