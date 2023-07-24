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

package hu.bme.mit.theta.llvm2xcfa.handlers.concrete;

import hu.bme.mit.theta.core.type.rattype.RatExprs;
import hu.bme.mit.theta.core.type.rattype.RatType;
import hu.bme.mit.theta.llvm2xcfa.handlers.BaseInstructionHandler;
import hu.bme.mit.theta.llvm2xcfa.handlers.Instruction;
import hu.bme.mit.theta.llvm2xcfa.handlers.arguments.Argument;
import hu.bme.mit.theta.llvm2xcfa.handlers.states.BlockState;
import hu.bme.mit.theta.llvm2xcfa.handlers.states.FunctionState;
import hu.bme.mit.theta.llvm2xcfa.handlers.states.GlobalState;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;
import static hu.bme.mit.theta.llvm2xcfa.Utils.foldExpression;

public class UnaryInstructionHandler extends BaseInstructionHandler {
    @Override
    public void handleInstruction(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        switch (instruction.getOpName()) {
            case "fneg":
                fneg(instruction, globalState, functionState, blockState);
                break;
            default:
                super.handleInstruction(instruction, globalState, functionState, blockState);
                break;
        }

    }

    private void fneg(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        Argument op1 = instruction.getArguments().get(0);

        checkState(op1.getType() == RatType.getInstance(), "Fneg only supports rational types!");
        checkState(instruction.getRetVar().isPresent(), "Instruction must have return variable");
        foldExpression(instruction, functionState, blockState, null, RatExprs.Neg(cast(op1.getExpr(functionState.getValues()), RatType.getInstance())), 0);

    }
}
