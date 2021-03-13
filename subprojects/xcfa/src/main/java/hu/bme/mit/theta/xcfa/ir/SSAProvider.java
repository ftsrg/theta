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
     * Name: The declared name of the global variable
     * Type: The type of the global variable, mapped to the IRType enum
     * Type_Value: The type and value of the global variable in a String, with a space in between (type is assumed to be in the LLVM printed format)
     */
    Collection<Tuple3<String, IRType, String>> getGlobalVariables();

    /*
     * Format: Tuple3<Name, RetType[0..1], Tuple2<Type, Name>[0..*]>
     * Name: The declared name of the function
     * RetType: The return type of the function, mapped to the IRType enum. Missing if the function is void.
     * Type: The type of the parameter
     * Name: The name of the parameter (generated or declared)
     */
    Collection<Tuple3<String, Optional<IRType>, List<Tuple2<IRType, String>>>> getFunctions();

    /*
     * Format: name
     * Name: Generated or declared name of the basic block.
     */
    List<String> getBlocks(String funcName);

    /*
     * Format: Tuple4<Opcode, Tuple2<RetType, RetVar>[0..1], Tuple2<VarType[0..1], VarName>[0..*], lineNumber>
     * Opcode: The instruction's opcode, mapped to the OpCode enum
     * RetType: Type of the instruction (~type of the resulting variable)
     * RetVar: Name of the resulting variable
     * VarType: Variable type *if argument is a variable*, empty otherwise
     * VarName: Variable name *if argument is a variable*, `type SPACE value` if constant, `value` if anything else (block, function, etc)
     */
    List<Tuple4<OpCode, Optional<Tuple2<IRType, String>>, List<Tuple2<Optional<IRType>, String>>, Integer>> getInstructions(String blockName);
}
