/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.solver.javasmt;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.SolverContext;

final class JavaSMTTransformationManager {

    private final JavaSMTTypeTransformer typeTransformer;
    private final JavaSMTDeclTransformer declTransformer;
    private final JavaSMTExprTransformer exprTransformer;

    public JavaSMTTransformationManager(
            final JavaSMTSymbolTable symbolTable, final SolverContext context) {
        this.typeTransformer = new JavaSMTTypeTransformer(context);
        this.declTransformer = new JavaSMTDeclTransformer(this, symbolTable, context);
        this.exprTransformer = new JavaSMTExprTransformer(this, symbolTable, context);
    }

    public FormulaType<?> toSort(final Type type) {
        return typeTransformer.toSort(type);
    }

    public Formula toSymbol(final Decl<?> decl) {
        return declTransformer.toSymbol(decl);
    }

    public Formula toTerm(final Expr<?> expr) {
        return exprTransformer.toTerm(expr);
    }

    public void reset() {
        // declTransformer does not have to be reset
        exprTransformer.reset();
    }
}
