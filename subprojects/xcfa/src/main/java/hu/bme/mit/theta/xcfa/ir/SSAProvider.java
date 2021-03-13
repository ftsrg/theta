package hu.bme.mit.theta.xcfa.ir;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.Tuple3;
import hu.bme.mit.theta.common.Tuple4;

import java.util.Collection;
import java.util.List;
import java.util.Optional;

public interface SSAProvider {

    /*
     * Format: Tuple3<Name, Type, Type_Value>
     */
    Collection<Tuple3<String, IRType, String>> getGlobalVariables();

    /*
     * Format: Tuple3<Name, RetType, Tuple2<Type, Name>[0..*]>
     * Not sure: param always of type Type
     */
    Collection<Tuple3<String, Optional<IRType>, List<Tuple2<IRType, String>>>> getFunctions();

    /*
     * Format: name
     */
    List<String> getBlocks(String funcName);

    /*
     * Format: Tuple4<Opcode, RetVar, Tuple2<VarType, Name>[0..*], lineNumber>
     */
    List<Tuple4<OpCode, Optional<Tuple2<IRType, String>>, List<Tuple2<Optional<IRType>, String>>, Integer>> getInstructions(String blockName);
}
