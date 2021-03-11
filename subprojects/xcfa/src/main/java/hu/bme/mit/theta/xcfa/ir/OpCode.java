package hu.bme.mit.theta.xcfa.ir;

public enum OpCode {
    // terminator
        RET,
        BR,
        SWITCH,
    // binary
        ADD,
        SUB,
        MUL,
        SDIV,
        SREM,
    // bitwise binary
        // NOT YET IMPLEMENTED
    // memory
        ALLOCA,
        LOAD,
        STORE,
        FENCE,
    // other
        ICMP,
        PHI,
        CALL

}
