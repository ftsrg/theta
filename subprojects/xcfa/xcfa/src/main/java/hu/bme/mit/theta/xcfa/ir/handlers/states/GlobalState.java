/*
 * Copyright 2021 Budapest University of Technology and Economics
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package hu.bme.mit.theta.xcfa.ir.handlers.states;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.Tuple3;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.xcfa.ir.ArithmeticType;
import hu.bme.mit.theta.xcfa.ir.SSAProvider;
import hu.bme.mit.theta.xcfa.model.XCFA;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.xcfa.ir.Utils.createConstant;
import static hu.bme.mit.theta.xcfa.ir.Utils.createVariable;

public class GlobalState {
    private final XCFA.Builder builder;
    private final Map<String, VarDecl<?>> globalVars;
    private final Map<String, String> processes;
    private final List<Tuple3<String, Optional<String>, List<Tuple2<String, String>>>> procedures;
    private final SSAProvider ssa;
    private final ArithmeticType arithmeticType;
    private int globalCounter = 0;

    public GlobalState(SSAProvider ssa, ArithmeticType arithmeticType) {
        this.ssa = ssa;
        if(arithmeticType == ArithmeticType.efficient && ssa.shouldUseBitwiseArithmetics()) arithmeticType = ArithmeticType.bitvector;
        else if(arithmeticType == ArithmeticType.efficient) arithmeticType = ArithmeticType.integer;
        checkState(!ssa.shouldUseBitwiseArithmetics() || arithmeticType == ArithmeticType.bitvector, "There are statements in the source not mappable to integer arithmetic");
        this.arithmeticType = arithmeticType;
        builder = XCFA.builder();
        this.globalVars = new HashMap<>();
        this.processes = new HashMap<>();
        this.procedures = new ArrayList<>();

        // Creating global variables
        for (Tuple3<String, String, String> globalVariable : ssa.getGlobalVariables()) {
            VarDecl<?> variable = createVariable(globalVariable.get1(), globalVariable.get2());
            globalVars.put(globalVariable.get1(), variable);
            builder.getGlobalVars().put(variable, Optional.of(createConstant(globalVariable.get3())));
        }

        procedures.addAll(ssa.getFunctions());

        processes.put("main", "main");

    }

    public void finalizeGlobalState(BuiltState builtState) {
    }

    public Map<String, VarDecl<?>> getGlobalVars() {
        return globalVars;
    }

    public void addGlobalVar(String name, VarDecl<?> globalVar) {
        this.globalVars.put(name, globalVar);
    }

    public Map<String, String> getProcesses() {
        return processes;
    }

    public void addProcess(String name, String mainProcedureName) {
        this.processes.put(name, mainProcedureName);
    }

    public int getGlobalCounter() {
        int cnt = globalCounter;
        ++globalCounter;
        return cnt;
    }

    public List<Tuple3<String, Optional<String>, List<Tuple2<String, String>>>> getProcedures() {
        return procedures;
    }

    public void addProcedure(Tuple3<String, Optional<String>, List<Tuple2<String, String>>> proc) {
        procedures.add(proc);
    }

    public SSAProvider getProvider() {
        return ssa;
    }

    public XCFA.Builder getBuilder() {
        return builder;
    }

    public ArithmeticType getArithmeticType() {
        return arithmeticType;
    }
}
