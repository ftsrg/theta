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

package hu.bme.mit.theta.llvm2xcfa.handlers;

import hu.bme.mit.theta.llvm2xcfa.ArithmeticType;
import hu.bme.mit.theta.llvm2xcfa.handlers.concrete.AggregateInstructionHandler;
import hu.bme.mit.theta.llvm2xcfa.handlers.concrete.ArrayIntrinsicsHandler;
import hu.bme.mit.theta.llvm2xcfa.handlers.concrete.BinaryInstructionHandler;
import hu.bme.mit.theta.llvm2xcfa.handlers.concrete.BitvectorInstructionHandler;
import hu.bme.mit.theta.llvm2xcfa.handlers.concrete.BitwiseInstructionHandler;
import hu.bme.mit.theta.llvm2xcfa.handlers.concrete.BuiltinFunctionHandler;
import hu.bme.mit.theta.llvm2xcfa.handlers.concrete.ConversionInstructionHandler;
import hu.bme.mit.theta.llvm2xcfa.handlers.concrete.MemoryInstructionHandler;
import hu.bme.mit.theta.llvm2xcfa.handlers.concrete.OtherInstructionHandler;
import hu.bme.mit.theta.llvm2xcfa.handlers.concrete.TerminatorInstructionHandler;
import hu.bme.mit.theta.llvm2xcfa.handlers.concrete.UnaryInstructionHandler;
import hu.bme.mit.theta.llvm2xcfa.handlers.concrete.VectorInstructionHandler;
import hu.bme.mit.theta.llvm2xcfa.handlers.concrete.checks.PointerArithmeticCheck;

import java.util.List;

public class InstructionHandlerManager {

    private static final List<Class<? extends InstructionHandler>> defaultInstructionHandlers = List.of(
            PointerArithmeticCheck.class,
            BuiltinFunctionHandler.class,
            ArrayIntrinsicsHandler.class,
            TerminatorInstructionHandler.class,
            UnaryInstructionHandler.class,
            BinaryInstructionHandler.class,
            BitwiseInstructionHandler.class,
            VectorInstructionHandler.class,
            AggregateInstructionHandler.class,
            MemoryInstructionHandler.class,
            ConversionInstructionHandler.class,
            OtherInstructionHandler.class
    );
    private static final List<Class<? extends InstructionHandler>> bitvectorInstructionHandlers = List.of(
            PointerArithmeticCheck.class,
            BitvectorInstructionHandler.class,
            BuiltinFunctionHandler.class,
            ArrayIntrinsicsHandler.class,
            TerminatorInstructionHandler.class,
            UnaryInstructionHandler.class,
            BinaryInstructionHandler.class,
            BitwiseInstructionHandler.class,
            VectorInstructionHandler.class,
            AggregateInstructionHandler.class,
            MemoryInstructionHandler.class,
            ConversionInstructionHandler.class,
            OtherInstructionHandler.class
    );
    private final List<Class<? extends InstructionHandler>> instructionHandlers;

    public InstructionHandlerManager(ArithmeticType arithmeticType) {
        if (arithmeticType == ArithmeticType.bitvector) {
            this.instructionHandlers = bitvectorInstructionHandlers;
        } else {
            this.instructionHandlers = defaultInstructionHandlers;
        }
    }

    public InstructionHandlerManager(List<Class<? extends InstructionHandler>> instructionHandlers) {
        this.instructionHandlers = instructionHandlers;
    }

    public static List<Class<? extends InstructionHandler>> getDefaultInstructionHandlers() {
        return defaultInstructionHandlers;
    }

    public InstructionHandler createInstructionHandlers() throws ReflectiveOperationException {
        InstructionHandler first = null;
        InstructionHandler last = null;
        for (Class<? extends InstructionHandler> instructionHandler : instructionHandlers) {
            InstructionHandler i = instructionHandler.getDeclaredConstructor().newInstance();
            if (last != null) last.setNext(i);
            else first = i;
            last = i;
        }
        return first;
    }
}
