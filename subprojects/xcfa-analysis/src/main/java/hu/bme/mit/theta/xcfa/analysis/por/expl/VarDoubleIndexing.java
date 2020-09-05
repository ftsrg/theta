/*
 *  Copyright 2017 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.xcfa.analysis.por.expl;

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.PrimeExpr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.utils.VarIndexing;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.XCFA.Process.Procedure;

import java.util.*;
import java.util.stream.Collectors;

import com.google.common.base.Preconditions;

/**
 * Supports 2 levels of indexing, one "indexing" for calls, one for multiple versions of the same variable.
 * Push/pop procedure handles the first level, specialized for this.
 * The remaining (get, inc) calls are for other uses, e.g. to create a SSA representation.
 * Note: this class is not immutable, unlike VarIndexing.
 */
public class VarDoubleIndexing {
    private final Map<XCFA.Process, ProcessStack> processes;

    private VarIndexing nonProcedureIndexing;
    /** Non-containment means that the variable is not a procedure-local variable */
    private final Map<VarDecl<?>, XCFA.Process> varToStack;

    private static final class ProcessStack {
        private final Stack<VarIndexing> indexingStack;

        private static ProcessStack copyOf(ProcessStack original) {
            // VarIndexing is final
            Stack<VarIndexing> indexingStack = new Stack<>();
            indexingStack.addAll(original.indexingStack);
            return new ProcessStack(indexingStack);
        }

        private ProcessStack(Stack<VarIndexing> indexingStack) {
            this.indexingStack = indexingStack;
        }

        public ProcessStack(ProcessState entryProcessState) {
            indexingStack = new Stack<>();
            indexingStack.push(VarIndexing.all(0));
            for (CallState s : entryProcessState.callStack()) {
                push(s.getProcedure());
            }
        }

        public void push(Procedure procedure) {
            var peek = indexingStack.peek();
            VarIndexing.Builder builder = peek.transform();
            for (var x: procedure.getLocalVars()) {
                builder.inc(x, +1);
            }
            for (var x: procedure.getParams()) {
                builder.inc(x, +1);
            }
            indexingStack.push(builder.build());
        }

        public void pop() {
            indexingStack.pop();
        }

        public int get(VarDecl<? extends Type> decl) {
            return indexingStack.peek().get(decl);
        }

        public void inc(VarDecl<? extends Type> decl, int modifier) {
            // replace last element in stack
            indexingStack.push(indexingStack.pop().inc(decl, modifier));
        }

        @Override
        public String toString() {
            return "ProcessStack{" +
                    "indexingStack=" + indexingStack.stream().map(VarIndexing::toString).collect(Collectors.joining()) +
                    '}';
        }
    }

    public static VarDoubleIndexing copyOf(VarDoubleIndexing indexing) {
        return new VarDoubleIndexing(indexing.nonProcedureIndexing, indexing.processes, indexing.varToStack);
    }

    private VarDoubleIndexing(VarIndexing nonProcedureIndexing, Map<XCFA.Process, ProcessStack> processes, Map<VarDecl<?>, XCFA.Process> varToStack) {
        this.nonProcedureIndexing = nonProcedureIndexing; // VarIndexing is immutable
        this.processes = new HashMap<>();
        this.varToStack = varToStack; // varToStack mapping does not change, as it relies only on XCFA structure
        for (var entry : processes.entrySet()) {
            this.processes.put(entry.getKey(), ProcessStack.copyOf(entry.getValue()));
        }
    }

    public VarDoubleIndexing(XCFA xcfa, ProcessStates initialProcessStates) {
        varToStack = new HashMap<>();
        processes = new HashMap<>();
        nonProcedureIndexing = VarIndexing.all(0);
        // initialize callstack
        for (var entry: initialProcessStates.getStates().entrySet()) {
            processes.put(entry.getKey(), new ProcessStack(entry.getValue()));
        }
        // initialize varToStack mapping
        for (var process : xcfa.getProcesses()) {
            for (var procedure : process.getProcedures()) {
                for (var param : procedure.getParams()) {
                    varToStack.put(param, process);
                }
                for (var localVar : procedure.getLocalVars()) {
                    varToStack.put(localVar, process);
                }
            }
        }
    }

    void pushProcedure(XCFA.Process parent, XCFA.Process.Procedure procedure) {
        Preconditions.checkArgument(parent.getProcedures().contains(procedure));
        processes.get(parent).push(procedure);
    }

    void popProcedure(XCFA.Process parent, XCFA.Process.Procedure procedure) {
        Preconditions.checkArgument(parent.getProcedures().contains(procedure));
        processes.get(parent).pop();
    }

    public int get(VarDecl<? extends Type> decl) {
        ProcessStack containingStack = processes.get(varToStack.get(decl));
        if (containingStack == null) {
            return nonProcedureIndexing.get(decl);
        }
        return containingStack.get(decl);
    }

    public void inc(VarDecl<? extends Type> decl, int modifier) {
        ProcessStack containingStack = processes.get(varToStack.get(decl));
        if (containingStack == null) {
            nonProcedureIndexing = nonProcedureIndexing.inc(decl);
            return;
        }
        containingStack.inc(decl, modifier);
    }

    public <DeclType extends Type> Expr<DeclType> unfold(Expr<DeclType> expr) {
        return unfold(expr, 0);
    }

    // specialized from StmtHelper
    public <DeclType extends Type> Expr<DeclType> unfold(Expr<DeclType> expr, int offset) {
        if (expr instanceof RefExpr) {
            final RefExpr<DeclType> ref = (RefExpr<DeclType>) expr;
            final Decl<DeclType> decl = ref.getDecl();
            if (decl instanceof VarDecl) {
                final VarDecl<DeclType> varDecl = (VarDecl<DeclType>) decl;
                final int index = get(varDecl) + offset;
                final ConstDecl<DeclType> constDecl = varDecl.getConstDecl(index);
                return constDecl.getRef();
            }
        }

        if (expr instanceof PrimeExpr) {
            final PrimeExpr<DeclType> prime = (PrimeExpr<DeclType>) expr;
            final Expr<DeclType> op = prime.getOp();
            return unfold(op, offset + 1);
        }

        return expr.map(op -> unfold(op, offset));
    }

    @Override
    public String toString() {
        return "VarDoubleIndexing{" +
                "(" + processes +
                "), nonProcedureIndexing=" + nonProcedureIndexing +
                '}';
    }
}
