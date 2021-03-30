package hu.bme.mit.theta.xcfa.ir.handlers;

import hu.bme.mit.theta.xcfa.ir.handlers.states.BlockState;
import hu.bme.mit.theta.xcfa.ir.handlers.states.FunctionState;
import hu.bme.mit.theta.xcfa.ir.handlers.states.GlobalState;

public interface InstructionHandler {

    void setNext(InstructionHandler instructionHandler);

    void handleInstruction(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState);

}
