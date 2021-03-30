package hu.bme.mit.theta.xcfa.ir.handlers;

import hu.bme.mit.theta.xcfa.ir.handlers.states.BlockState;
import hu.bme.mit.theta.xcfa.ir.handlers.states.FunctionState;
import hu.bme.mit.theta.xcfa.ir.handlers.states.GlobalState;

public abstract class BaseInstructionHandler implements InstructionHandler{

    private InstructionHandler next;

    @Override
    public void setNext(InstructionHandler instructionHandler) {
        next = instructionHandler;
    }

    @Override
    public void handleInstruction(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        if(next != null) next.handleInstruction(instruction, globalState, functionState, blockState);
    }
}
