package hu.bme.mit.theta.xcfa.ir;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.Tuple4;
import hu.bme.mit.theta.xcfa.XCFA;

import java.util.List;
import java.util.Map;
import java.util.Optional;

public interface InstructionHandler {

    void handleInstruction(Tuple4<String, Optional<Tuple2<String, String>>, List<Tuple2<Optional<String>, String>>, Integer> instruction);

    void reinitClass(String block);

    void substituteProcedures(Map<String, XCFA.Process.Procedure> procedures);

    void endProcedure();
}
