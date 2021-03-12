package hu.bme.mit.theta.xcfa.ir;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.Tuple4;

import java.util.List;
import java.util.Optional;

public interface InstructionHandler {

    void handleInstruction(Tuple4<OpCode, Optional<String>, List<Tuple2<Optional<IRType>, String>>, Integer> instruction);

    void reinitClass(String block);
}
