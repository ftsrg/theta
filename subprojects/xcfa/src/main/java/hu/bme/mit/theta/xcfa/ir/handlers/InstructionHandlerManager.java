package hu.bme.mit.theta.xcfa.ir.handlers;

import hu.bme.mit.theta.xcfa.ir.handlers.concrete.*;

import java.util.List;

public class InstructionHandlerManager {

    private static final List<Class<? extends InstructionHandler>> defaultInstructionHandlers = List.of(
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

    public static List<Class<? extends InstructionHandler>> getDefaultInstructionHandlers() {
        return defaultInstructionHandlers;
    }

    private final List<Class<? extends InstructionHandler>> instructionHandlers;

    public InstructionHandlerManager() {
        this.instructionHandlers = defaultInstructionHandlers;
    }
    public InstructionHandlerManager(List<Class<? extends InstructionHandler>> instructionHandlers) {
        this.instructionHandlers = instructionHandlers;
    }

    public InstructionHandler createInstructionHandlers() throws ReflectiveOperationException {
        InstructionHandler first = null;
        InstructionHandler last = null;
        for (Class<? extends InstructionHandler> instructionHandler : instructionHandlers) {
            InstructionHandler i = instructionHandler.getDeclaredConstructor().newInstance();
            if(last != null) last.setNext(i);
            else first = i;
            last = i;
        }
        return first;
    }
}
