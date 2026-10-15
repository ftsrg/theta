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

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.type.Expr;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.SolverContext;

/**
 * Converts JavaSMT formulas created outside Theta (e.g. parsed from SMT-LIB text) into Theta
 * expressions. Every free constant of a converted formula must be registered first.
 */
public final class JavaSMTFormulaConverter {

    private final JavaSMTSymbolTable symbolTable = new JavaSMTSymbolTable();
    private final JavaSMTTermTransformer transformer;

    public JavaSMTFormulaConverter(SolverContext context) {
        this.transformer = new JavaSMTTermTransformer(symbolTable, context, true);
    }

    /** Makes {@code constDecl} the Theta counterpart of the JavaSMT constant {@code symbol}. */
    public void register(ConstDecl<?> constDecl, Formula symbol) {
        symbolTable.put(constDecl, symbol);
    }

    public Expr<?> toExpr(Formula formula) {
        return transformer.toExpr(formula);
    }
}
