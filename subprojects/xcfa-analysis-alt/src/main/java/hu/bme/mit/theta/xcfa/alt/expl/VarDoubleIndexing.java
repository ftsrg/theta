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

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.VarIndexing;
import hu.bme.mit.theta.xcfa.XCFA;

import java.util.Stack;

/**
 * Supports 2 levels of indexing, one "indexing" for calls, one for multiple versions of the same variable.
 * Push/pop procedure handles the first level, specialized for this.
 * The remaining (get, inc) calls are for other uses, e.g. to create a SSA representation.
 * Note: this class is not immutable, unlike VarIndexing.
 */
public class VarDoubleIndexing {
    private final Stack<VarIndexing> indexingStack = new Stack<>();

    public VarDoubleIndexing() {
        indexingStack.push(VarIndexing.all(0));
    }

    void pushProcedure(XCFA.Process.Procedure procedure) {
        var peek = indexingStack.peek();
        VarIndexing.Builder builder = peek.transform();
        for (var x: procedure.getLocalVars()) {
            builder.inc(x, +1);
        }
        for (var x: procedure.getParams()) {
            builder.inc(x, +1);
        }
        indexingStack.push(peek);
    }

    void popProcedure() {
        indexingStack.pop();
    }

    public int get(VarDecl<? extends Type> var) {
        return indexingStack.peek().get(var);
    }

    public void inc(VarDecl<? extends Type> decl, int modifier) {
        // replace last element in stack
        indexingStack.push(indexingStack.pop().inc(decl, modifier));
    }

    public <DeclType extends Type> Expr<DeclType> unfold(Expr<DeclType> expr) {
        return PathUtils.unfold(expr, indexingStack.peek());
    }
}
