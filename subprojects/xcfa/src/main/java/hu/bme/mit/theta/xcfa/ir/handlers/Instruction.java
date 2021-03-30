package hu.bme.mit.theta.xcfa.ir.handlers;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.Tuple4;
import hu.bme.mit.theta.xcfa.ir.handlers.arguments.Argument;
import hu.bme.mit.theta.xcfa.ir.handlers.arguments.RegArgument;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import static com.google.common.base.Preconditions.checkState;

public class Instruction {
    private final String opName;
    private final Optional<RegArgument> retVar;
    private final List<Argument> arguments;
    private final Integer lineNumber;

    public Instruction(Tuple4<String, Optional<Tuple2<String, String>>, List<Tuple2<Optional<String>, String>>, Integer> instr) {
        Argument arg = null;
        if(instr.get2().isPresent()) {
            arg = Argument.of(instr.get2().get().get1(), instr.get2().get().get2());
            checkState(arg instanceof RegArgument, "Argument not instance of RegArgument!");
        }
        this.opName = instr.get1();
        this.retVar = instr.get2().isPresent() ? Optional.ofNullable((RegArgument) arg) : Optional.empty();
        this.arguments = new ArrayList<>();
        for (Tuple2<Optional<String>, String> objects : instr.get3()) {
            this.arguments.add(Argument.of(objects.get1().orElse(""), objects.get2()));
        }
        this.lineNumber = instr.get4();
    }

    public String getOpName() {
        return opName;
    }

    public Optional<RegArgument> getRetVar() {
        return retVar;
    }

    public List<Argument> getArguments() {
        return arguments;
    }

    public Integer getLineNumber() {
        return lineNumber;
    }
}
