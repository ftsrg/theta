package hu.bme.mit.theta.xcfa.ir;

import java.util.*;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.Tuple3;
import hu.bme.mit.theta.common.Tuple4;

public class LlvmIrProvider implements SSAProvider {
    static {
        System.loadLibrary("irParser");
    }

    private Map<String, Integer> bbNamefuncIndexLut; // key: BasicBlock name, value: index of function in module

    private native void JniParseIr(String irFilename);

    LlvmIrProvider(String irFilename) {
        JniParseIr(irFilename);
        bbNamefuncIndexLut = new HashMap<>();

        int numOfFunctions = JniGetFunctionsNum();

        for(int f = 0; f < numOfFunctions; f++) {
            String functionName = JniGetFunctionName(f);
            int numOfBasicBlocks = JniGetNumOfBasicBlocks(f);

            for(int b = 0; b < numOfBasicBlocks; b++) {
                bbNamefuncIndexLut.put(JniGetBlockName(f, b), f);
            }
        }

    }

    // Format: Tuple3<Name, Type, Value>
    @Override
    public Collection<Tuple3<String, String, String>> getGlobalVariables() {
        // TODO
        /*
        int numOfGlobalVar = JniGetGlobalVariablesNum();
        Tuple3<String, IRType, String> globalVar;
        ArrayList<Tuple3<String, IRType, String>> globalVarList = new ArrayList<Tuple3<String, IRType, String>>();

        for(int i = 0; i < numOfGlobalVar; i++) {
            globalVar = new Tuple3<>(
                JniGetGlobalVariableName(i),
                JniGetGlobalVariableType(i),
                JniGetGlobalVariableValue(i)
            );
            globalVarList.add(globalVar);
        }
        return globalVarList; */
        return null;
    }

    private native int JniGetFunctionsNum();
    private native String JniGetFunctionRetType(int funcIndex);
    private native String JniGetFunctionName(int funcIndex);
    private native int JniGetNumOfFunctionParameters(int funcIndex);
    private native String JniGetParameterType(int funcIndex, int paramIndex);
    private native String JniGetParameterName(int funcIndex, int paramIndex);

    @Override
    public Collection<Tuple3<String, Optional<String>, List<Tuple2<String, String>>>> getFunctions() {
        int numOfFunctions = JniGetFunctionsNum();
        ArrayList<Tuple3<String, Optional<String>, List<Tuple2<String, String>>>> functions = new ArrayList<>();

        for(int f = 0; f < numOfFunctions; f++) {
            String functionName = JniGetFunctionName(f);
            String retType = JniGetFunctionRetType(f); // TODO make this really optional? (->when void)
            int numOfParams = JniGetNumOfFunctionParameters(f);

            ArrayList<Tuple2<String, String>> parameters = new ArrayList<>();
            for(int p = 0; p < numOfParams; p++) {
                String paramType = JniGetParameterType(f, p);
                String paramName = JniGetParameterName(f, p);
                parameters.add(Tuple2.of(paramType, paramName));
            }
            if(retType.equals("void")) {
                functions.add(Tuple3.of(functionName, Optional.of(retType), parameters));
            } else {
                functions.add(Tuple3.of(functionName, Optional.empty(), parameters));
            }
        }
        return functions;
    }

    private native int JniGetNumOfBasicBlocks(int funcIndex);
    private native int JniGetFunctionIndex(String funcName);
    private native String JniGetBlockName(int funcIndex, int BasicBlockIndex);

    @Override
    public List<String> getBlocks(String funcName) {
        int f = JniGetFunctionIndex(funcName);
        int numOfBasicBlocks = JniGetNumOfBasicBlocks(f);
        ArrayList<String> blocks = new ArrayList<>();
        for(int b = 0; b < numOfBasicBlocks; b++) {
            blocks.add(JniGetBlockName(f, b));
        }
        return blocks;
    }

    private native int JniGetBlockIndex(int functionIndex, String blockName);
    private native int JniGetNumOfInstructions(int functionIndex, int basicBlockIndex);
    private native int JniGetInstructionLineNumber(int functionIndex, int basicBlockIndex, int i);
    private native String JniGetInstructionOpcode(int functionIndex, int basicBlockIndex, int i);
    private native String JniGetInstructionRetType(int functionIndex, int basicBlockIndex, int i);
    private native String JniGetInstructionRetName(int functionIndex, int basicBlockIndex, int i);
    private native int JniGetInstructionNumOfOperands(int functionIndex, int basicBlockIndex, int i);
    private native String JniGetInstructionOperandVarType(int functionIndex, int basicBlockIndex, int i, int o);
    private native String JniGetInstructionOperandVarName(int functionIndex, int basicBlockIndex, int i, int o);

    @Override
    public List<Tuple4<String, Optional<Tuple2<String, String>>, List<Tuple2<Optional<String>, String>>, Integer>> getInstructions(String blockName) {
        int functionIndex = bbNamefuncIndexLut.get(blockName);
        int basicBlockIndex = JniGetBlockIndex(functionIndex, blockName);
        int numOfInstructions = JniGetNumOfInstructions(functionIndex, basicBlockIndex);

        ArrayList<Tuple4<String, Optional<Tuple2<String, String>>, List<Tuple2<Optional<String>, String>>, Integer>> instructions = new ArrayList<>();
        for(int i = 0; i < numOfInstructions; i++) {
            int lineNumber = JniGetInstructionLineNumber(functionIndex, basicBlockIndex, i);
            String opcode = JniGetInstructionOpcode(functionIndex, basicBlockIndex, i);
            String retType = JniGetInstructionRetType(functionIndex, basicBlockIndex, i);
            String retVar = JniGetInstructionRetName(functionIndex, basicBlockIndex, i);
            int numOfOperands = JniGetInstructionNumOfOperands(functionIndex, basicBlockIndex, i);
            ArrayList<Tuple2<Optional<String>, String>> instructionOperands = new ArrayList<>();
            for(int o = 0; o < numOfOperands; o++) {
                String varType = JniGetInstructionOperandVarType(functionIndex, basicBlockIndex, i, o); // TODO make it optional
                String varName = JniGetInstructionOperandVarName(functionIndex, basicBlockIndex, i, o);
                if(varType.equals("constant")) {
                    instructionOperands.add(Tuple2.of(Optional.empty(), varName));
                } else {
                    instructionOperands.add(Tuple2.of(Optional.of(varType), varName));
                }
            }

            if(retType.equals("")) {
                instructions.add(Tuple4.of(opcode, Optional.empty(), instructionOperands, lineNumber));
            } else {
                instructions.add(Tuple4.of(opcode, Optional.of(Tuple2.of(retType, retVar)), instructionOperands, lineNumber));
            }
        }

        return instructions;
    }

}