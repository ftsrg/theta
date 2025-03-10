/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.llvm2xcfa.handlers.concrete;

import hu.bme.mit.theta.llvm2xcfa.handlers.BaseInstructionHandler;
import hu.bme.mit.theta.llvm2xcfa.handlers.Instruction;
import hu.bme.mit.theta.llvm2xcfa.handlers.states.BlockState;
import hu.bme.mit.theta.llvm2xcfa.handlers.states.FunctionState;
import hu.bme.mit.theta.llvm2xcfa.handlers.states.GlobalState;

public class VectorInstructionHandler extends BaseInstructionHandler {
    @Override
    public void handleInstruction(
            Instruction instruction,
            GlobalState globalState,
            FunctionState functionState,
            BlockState blockState) {
        switch (instruction.getOpName()) {
            case "extractelement":
                extractelement(instruction, globalState, functionState, blockState);
                break;
            case "insertelement":
                insertelement(instruction, globalState, functionState, blockState);
                break;
            case "shufflevector":
                break;
            default:
                super.handleInstruction(instruction, globalState, functionState, blockState);
                break;
        }
    }

    private void insertelement(
            Instruction instruction,
            GlobalState globalState,
            FunctionState functionState,
            BlockState blockState) {

        throw new RuntimeException("Not yet implemented!");
    }

    private void extractelement(
            Instruction instruction,
            GlobalState globalState,
            FunctionState functionState,
            BlockState blockState) {
        throw new RuntimeException("Not yet implemented!");
    }
}
