## JNI Interface
*"In software design, the Java Native Interface (JNI) is a foreign function interface programming framework that enables Java code running in a Java virtual machine (JVM) to call and be called by native applications (programs specific to a hardware and operating system platform) and libraries written in other languages such as C, C++ and assembly."* (from [wikipedia](https://en.wikipedia.org/wiki/Java_Native_Interface))

This project behaves as a native library of the Theta framework and communicates through a JNI interface. Although it is possible to send objects through a native interface, we are currently not using that feature. 

The easiest way to get familiar with the interface is to check out the C++ side [here](https://github.com/ftsrg/theta-c-frontend/blob/master/src/hu_bme_mit_theta_llvm2xcfa_LlvmIrProvider.h) and the Java side in Theta (`LllvmIrProvider` class of the XCFA subproject).

### Configuring passes and parsing the input program
Currently there are four switches to configure pass groups (the rest of the passes are mandatory).
- Function inlining (we do not inline global variables)
- Cleanup passes
- Optimizations
- Debug printing pass

After configuration the native function `JniParseIr` has to be called to let the frontend iterate through the LLVM IR.

### Querying the resulting data
The data can be queried based on these groups:
- global variables
- functions
    - basic blocks
        - instructions

The number of these in a given parent and their attributes can be queried one by one.
Furthermore analysis results can be queried as well.
