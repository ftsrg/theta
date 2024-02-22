#include "hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider.h"
#include "types/Module.h"
#include "utilities/CPipeline.h"
#include "utilities/Analysis.h"
#include "types/BasicBlock.h"
#include "types/operands/Register.h"

// NOTE: don't use CLions automatic code formatting, it handles this part pretty badly

/*
 * Class:     hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider
 * Method:    JniParseIr
 * Signature: (Ljava/lang/String;)V
 */
JNIEXPORT void JNICALL
Java_hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider_JniParseIr(JNIEnv* env, jobject, jstring filename) {
    Analysis::reset();
    BasicBlock::reset();
    Register::reset();

    // Convert the JNI String (jstring) into C-String (char*)
    const char *cFilename = env->GetStringUTFChars(filename, NULL);
    if (NULL == cFilename) {
        std::cout << "Could not get filename from jenv!" << std::endl;
        return;
    }


    // (compile and) parse into llvm Module
    std::unique_ptr <llvm::Module> llvmModule;
    llvm::SMDiagnostic error;
    std::string strFilename(cFilename);
    std::string filenameExtension = strFilename.substr(strFilename.length() - 2, strFilename.length());

    if (  filenameExtension.compare(".c") || filenameExtension.compare(".i")) {
        CPipeline cp = CPipeline(strFilename, "/usr/bin/clang");
        llvmModule = cp.processCProgram();
    } else {
        llvmModule = parseIRFile(cFilename, error, context);
    }

    if(llvmModule==nullptr) {
        std::cout << "Error while parsing: null module!" << std::endl;
        return; // TODO somehow communicate the error better
    }

    // print the IR into a file - for debugging purposes
    if(PassGroupManager::debugPrintIr==true) {
        std::error_code EC;
        llvm::raw_fd_ostream outIr(strFilename + ".before.ll", EC);
        llvmModule->print(outIr, nullptr);
    }

    // parse from llvm module to our own module
    Module &module = Module::getModule();
    module.parseLLVMModule(move(llvmModule));
    // module.print(); // for debugging purposes
    // Register::printLUT(); // for debugging purposes

    env->ReleaseStringUTFChars(filename, cFilename);  // release string resources
}

/*
 * Class:     hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider
 * Method:    JniDisableInlining
 * Signature: ()V
 */
JNIEXPORT void JNICALL
Java_hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider_JniDisableInlining
(JNIEnv*, jobject) {
    PassGroupManager::enableInlining = false;
}

/*
 * Class:     hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider
 * Method:    JniDisableOptimizationPasses
 * Signature: ()V
 */
JNIEXPORT void JNICALL
Java_hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider_JniDisableOptimizationPasses
(JNIEnv*, jobject) {
    PassGroupManager::enableOptimizations = false;
}

/*
 * Class:     hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider
 * Method:    JniDisableCleanupPasses
 * Signature: ()V
 */
JNIEXPORT void JNICALL
Java_hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider_JniDisableCleanupPasses
(JNIEnv*, jobject) {
    PassGroupManager::enableCleanupPasses = false;
}

/*
 * Class:     hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider
 * Method:    JniDisablePrintDebugIr
 * Signature: ()V
 */
JNIEXPORT void JNICALL
Java_hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider_JniDisablePrintDebugIr
(JNIEnv*, jobject) {
    PassGroupManager::debugPrintIr = false;
}

/*
 * Class:     hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider
 * Method:    JniGetGlobalVariablesNum
 * Signature: ()I
 */
JNIEXPORT jint

JNICALL Java_hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider_JniGetGlobalVariablesNum
(JNIEnv * env, jobject) {
    Module &module = Module::getModule();
    return (jint)module.getNumOfGlobalVariables();
}

/*
 * Class:     hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider
 * Method:    JniGetGlobalVariableName
 * Signature: (I)Ljava/lang/String;
 */
JNIEXPORT jstring
JNICALL Java_hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider_JniGetGlobalVariableName
(JNIEnv * env, jobject, jint g) {
    Module &module = Module::getModule();
    int globalVarIndex = (int) g;
    return env->NewStringUTF((module.getGlobalVariable(globalVarIndex)->getName()).c_str());
}

/*
 * Class:     hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider
 * Method:    JniGetGlobalVariableType
 * Signature: (I)Ljava/lang/String;
 */
JNIEXPORT jstring
JNICALL Java_hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider_JniGetGlobalVariableType
(JNIEnv * env, jobject, jint g) {
    Module &module = Module::getModule();
    int globalVarIndex = (int) g;
    return env->
    NewStringUTF((module.getGlobalVariable(globalVarIndex)->getType()).c_str());
}

/*
 * Class:     hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider
 * Method:    JniGetGlobalVariableValue
 * Signature: (I)Ljava/lang/String;
 */
JNIEXPORT jstring
JNICALL Java_hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider_JniGetGlobalVariableValue
(JNIEnv * env, jobject, jint g) {
    Module &module = Module::getModule();
    int globalVarIndex = (int) g;
    return env->NewStringUTF((module.getGlobalVariable(globalVarIndex)->getInitialValue()).c_str());
}

/*
 * Class:     hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider
 * Method:    JniGetFunctionsNum
 * Signature: ()I
 */
JNIEXPORT jint

JNICALL Java_hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider_JniGetFunctionsNum
(JNIEnv * env, jobject) {
    Module &module = Module::getModule();
    return (jint)
    module.getNumOfFunctions();
}

/*
 * Class:     hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider
 * Method:    JniGetFunctionRetType
 * Signature: (I)Ljava/lang/String;
 */
JNIEXPORT jstring
JNICALL Java_hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider_JniGetFunctionRetType
(JNIEnv * env, jobject, jint f) {
    Module &module = Module::getModule();
    int functionIndex = (int) f;
    std::string retType = module.getFunction(functionIndex)->getReturnType();
    return env->NewStringUTF(retType.c_str());
}

/*
 * Class:     hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider
 * Method:    JniGetFunctionName
 * Signature: (I)Ljava/lang/String;
 */
JNIEXPORT jstring
JNICALL Java_hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider_JniGetFunctionName
(JNIEnv * env, jobject, jint f) {
    Module &module = Module::getModule();
    int functionIndex = (int) f;
    return env->NewStringUTF((module.getFunction(functionIndex)->getName()).c_str());
}

/*
 * Class:     hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider
 * Method:    JniGetNumOfFunctionParameters
 * Signature: (I)I
 */
JNIEXPORT jint
JNICALL Java_hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider_JniGetNumOfFunctionParameters
(JNIEnv * env, jobject, jint f) {
    Module &module = Module::getModule();
    int functionIndex = (int) f;
    return (jint)module.getFunction(functionIndex)->getNumOfParameters();
}

/*
 * Class:     hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider
 * Method:    JniGetParameterType
 * Signature: (II)Ljava/lang/String;
 */
JNIEXPORT jstring
JNICALL Java_hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider_JniGetParameterType
(JNIEnv * env, jobject, jint f, jint p) {
    Module &module = Module::getModule();
    int functionIndex = (int) f;
    int paramIndex = (int) p;
    return env->NewStringUTF((module.getFunction(functionIndex)->getParameter(paramIndex)->getType()).c_str());
}

/*
 * Class:     hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider
 * Method:    JniGetParameterName
 * Signature: (II)Ljava/lang/String;
 */
JNIEXPORT jstring
JNICALL Java_hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider_JniGetParameterName
(JNIEnv * env, jobject, jint f, jint p) {
    Module &module = Module::getModule();
    int functionIndex = (int) f;
    int paramIndex = (int) p;
    return env->NewStringUTF((module.getFunction(functionIndex)->getParameter(paramIndex)->getName()).c_str());
}

/*
 * Class:     hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider
 * Method:    JniGetNumOfBasicBlocks
 * Signature: (I)I
 */
JNIEXPORT jint
JNICALL Java_hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider_JniGetNumOfBasicBlocks
(JNIEnv * env, jobject, jint f) {
    Module &module = Module::getModule();
    int functionIndex = (int) f;
    return (jint)module.getFunction(functionIndex)->getNumOfBasicBlocks();
}

/*
 * Class:     hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider
 * Method:    JniGetFunctionIndex
 * Signature: (Ljava/lang/String;)I
 */
JNIEXPORT jint
JNICALL Java_hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider_JniGetFunctionIndex
(JNIEnv * env, jobject, jstring functionName) {
    Module &module = Module::getModule();
    // Convert the JNI String (jstring) into C-String (char*)
    const char *cFunctionName = env->GetStringUTFChars(functionName, NULL);
    if (NULL == cFunctionName) return -1; // ERROR TODO (communicate somehow better?)
    int funcIndex = module.findFunctionByName(cFunctionName);
    env->ReleaseStringUTFChars(functionName, cFunctionName);  // release string resources

    return (jint)
    funcIndex;
}

/*
 * Class:     hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider
 * Method:    JniGetBlockName
 * Signature: (II)Ljava/lang/String;
 */
JNIEXPORT jstring
JNICALL Java_hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider_JniGetBlockName
(JNIEnv * env, jobject, jint f, jint b) {
    Module &module = Module::getModule();
    int functionIndex = (int) f;
    int basicBlockIndex = (int) b;
    return env->NewStringUTF((module.getFunction(functionIndex)->getBasicBlock(basicBlockIndex)->getName()).c_str());
}

/*
 * Class:     hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider
 * Method:    JniGetBlockIndex
 * Signature: (ILjava/lang/String;)I
 */
JNIEXPORT jint
JNICALL Java_hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider_JniGetBlockIndex
(JNIEnv * env, jobject, jint f, jstring basicBlockName) {
    Module &module = Module::getModule();

    // Convert the JNI String (jstring) into C-String (char*)
    const char *cBasicBlockName = env->GetStringUTFChars(basicBlockName, NULL);
    if (NULL == cBasicBlockName) return -1; // ERROR TODO (communicate somehow better?)

    int basicBlockIndex = module.getFunction(f)->findBasicBlockByName(cBasicBlockName);

    env->ReleaseStringUTFChars(basicBlockName, cBasicBlockName);  // release string resources

    return (jint)
    basicBlockIndex;
}

/*
 * Class:     hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider
 * Method:    JniGetNumOfInstructions
 * Signature: (II)I
 */
JNIEXPORT jint
JNICALL Java_hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider_JniGetNumOfInstructions
(JNIEnv * env, jobject, jint f, jint b) {
    Module &module = Module::getModule();
    int functionIndex = (int) f;
    int bbIndex = (int) b;
    return (jint)module.getFunction(functionIndex)->getBasicBlock(bbIndex)->

    getNumOfInstructions();
}

/*
 * Class:     hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider
 * Method:    JniGetInstructionLineNumber
 * Signature: (III)I
 */
JNIEXPORT jint
JNICALL Java_hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider_JniGetInstructionLineNumber
(JNIEnv * env, jobject, jint f, jint b, jint i) {
    Module &module = Module::getModule();
    int functionIndex = (int) f;
    int bbIndex = (int) b;
    int instIndex = (int) i;
    return (jint)module.getFunction(functionIndex)->getBasicBlock(bbIndex)->getInstruction(instIndex)->getLineNumber();
}

/*
 * Class:     hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider
 * Method:    JniGetInstructionOpcode
 * Signature: (III)Ljava/lang/String;
 */
JNIEXPORT jstring
JNICALL Java_hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider_JniGetInstructionOpcode
(JNIEnv * env, jobject, jint f, jint b, jint i) {
    Module &module = Module::getModule();
    int functionIndex = (int) f;
    int bbIndex = (int) b;
    int instIndex = (int) i;
    std::string opName = module.getFunction(functionIndex)->getBasicBlock(bbIndex)->getInstruction(instIndex)->getOpname();
    return env->NewStringUTF( opName.c_str() );
}

/*
 * Class:     hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider
 * Method:    JniGetInstructionRetType
 * Signature: (III)Ljava/lang/String;
 */
JNIEXPORT jstring
JNICALL Java_hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider_JniGetInstructionRetType
(JNIEnv * env, jobject, jint f, jint b, jint i) {
    Module &module = Module::getModule();
    int functionIndex = (int) f;
    int bbIndex = (int) b;
    int instIndex = (int) i;
    std::shared_ptr <Register> reg = module.getFunction(functionIndex)->getBasicBlock(bbIndex)->getInstruction(instIndex)->getRetVariable();
    std::string retType;
    if ( reg ) retType = reg->getType();
    else {
        retType = "";
    }
    return env->NewStringUTF( retType.c_str() );
}

/*
 * Class:     hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider
 * Method:    JniGetInstructionRetName
 * Signature: (III)Ljava/lang/String;
 */
JNIEXPORT jstring
JNICALL Java_hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider_JniGetInstructionRetName
(JNIEnv * env, jobject, jint f, jint b, jint i) {
    Module &module = Module::getModule();
    int functionIndex = (int) f;
    int bbIndex = (int) b;
    int instIndex = (int) i;
    std::shared_ptr <Register> reg = module.getFunction(functionIndex)->getBasicBlock(bbIndex)->getInstruction(instIndex)->getRetVariable();
    std::string retName;
    if ( reg ) {
        retName = reg->getName();
    } else {
        retName = "";
    }
    return env->NewStringUTF( retName.c_str());
}

/*
 * Class:     hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider
 * Method:    JniGetInstructionNumOfOperands
 * Signature: (III)I
 */
JNIEXPORT jint
JNICALL Java_hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider_JniGetInstructionNumOfOperands
(JNIEnv * env, jobject, jint f, jint b, jint i) {
    Module &module = Module::getModule();
    int functionIndex = (int) f;
    int bbIndex = (int) b;
    int instIndex = (int) i;
    int numOfOperands = module.getFunction(functionIndex)->getBasicBlock(bbIndex)->getInstruction(instIndex)->getNumOfOperands();
    return (jint)numOfOperands;
}

/*
 * Class:     hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider
 * Method:    JniGetInstructionOperandVarType
 * Signature: (IIII)Ljava/lang/String;
 */
JNIEXPORT jstring
JNICALL Java_hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider_JniGetInstructionOperandVarType
(JNIEnv * env, jobject, jint f, jint b, jint i, jint o) {
    Module &module = Module::getModule();
    int functionIndex = (int) f;
    int bbIndex = (int) b;
    int instIndex = (int) i;
    int operandIndex = (int) o;
    std::string operandType;

    // only registers will return a proper type, all others return constant, this is then handled on the Java side in the SSAProvider
    operandType = module.getFunction(functionIndex)->getBasicBlock(bbIndex)->getInstruction(instIndex)->getOperand(operandIndex)->getType();
    return env->NewStringUTF( operandType.c_str() );
}

/*
 * Class:     hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider
 * Method:    JniGetInstructionOperandVarName
 * Signature: (IIII)Ljava/lang/String;
 */
JNIEXPORT jstring
JNICALL Java_hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider_JniGetInstructionOperandVarName
(JNIEnv * env, jobject, jint f, jint b, jint i, jint o ) {
    Module &module = Module::getModule();
    int functionIndex = (int) f;
    int bbIndex = (int) b;
    int instIndex = (int) i;
    int operandIndex = (int) o;
    std::string operandName = module.getFunction(functionIndex)->getBasicBlock(bbIndex)->getInstruction(instIndex)->getOperand(operandIndex)->getName();
    return env->NewStringUTF( operandName.c_str());
}

/*
 * Class:     hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider
 * Method:    JniGetStructAnalysisResult
 * Signature: ()I
 */
JNIEXPORT jboolean
JNICALL Java_hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider_JniGetStructAnalysisResult
(JNIEnv * env, jobject) {
    return (jboolean)Analysis::getStructAnalysisResult();
}

/*
 * Class:     hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider
 * Method:    JniGetBitwiseArithmeticAnalysisResult
 * Signature: ()I
 */
JNIEXPORT jboolean
JNICALL Java_hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider_JniGetBitwiseArithmeticAnalysisResult
(JNIEnv * env, jobject) {
    return (jboolean)Analysis::getBitwiseOpAnalysisResult();
}
