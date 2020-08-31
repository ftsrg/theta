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
package hu.bme.mit.theta.xcfa.alt.expl;

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

import java.util.HashMap;
import java.util.Map;
import java.util.Stack;

import com.google.common.base.Preconditions;

/**
 * Supports 2 levels of indexing, one "indexing" for calls, one for multiple versions of the same variable.
 * Push/pop procedure handles the first level, specialized for this.
 * The remaining (get, inc) calls are for other uses, e.g. to create a SSA representation.
 * Note: this class is not immutable, unlike VarIndexing.
 */
public class VarDoubleIndexing {
    private static final class ProcessStack {
        private final Stack<VarIndexing> indexingStack = new Stack<>();

        public ProcessStack(ProcessState entryProcessState) {
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
    }

    Map<XCFA.Process, ProcessStack> processes = new HashMap<>();

    VarIndexing nonProcedureIndexing = VarIndexing.all(0);
    /** Non-containment means that the variable is not a procedure-local variable */
    Map<VarDecl<?>, ProcessStack> varToStack = new HashMap<>();

    public VarDoubleIndexing(XCFA xcfa, ProcessStates initialProcessStates) {
        // initialize callstack
        for (var entry: initialProcessStates.getStates().entrySet()) {
            processes.put(entry.getKey(), new ProcessStack(entry.getValue()));
        }
        // initialize varToStack mapping
        for (var process : xcfa.getProcesses()) {
            for (var procedure : process.getProcedures()) {
                for (var localVar : procedure.getLocalVars()) {
                    varToStack.put(localVar, processes.get(process));
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
        ProcessStack containingStack = varToStack.get(decl);
        if (containingStack == null) {
            return nonProcedureIndexing.get(decl);
        }
        return containingStack.get(decl);
    }

    public void inc(VarDecl<? extends Type> decl, int modifier) {
        ProcessStack containingStack = varToStack.get(decl);
        if (containingStack == null) {
            nonProcedureIndexing.inc(decl);
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
                final RefExpr<DeclType> refExpr = constDecl.getRef();
                return refExpr;
            }
        }

        if (expr instanceof PrimeExpr) {
            final PrimeExpr<DeclType> prime = (PrimeExpr<DeclType>) expr;
            final Expr<DeclType> op = prime.getOp();
            return unfold(op, offset + 1);
        }

        return expr.map(op -> unfold(op, offset));
    }
}
