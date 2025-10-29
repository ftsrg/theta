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
package hu.bme.mit.theta.solver.eldarica;

import ap.types.Sort;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;

public final class EldaricaTransformationManager {
    private final EldaricaTypeTransformer typeTransformer;
    private final EldaricaDeclTransformer declTransformer;
    private final EldaricaExprTransformer exprTransformer;

    public EldaricaTransformationManager(final EldaricaSymbolTable symbolTable) {
        this.typeTransformer = new EldaricaTypeTransformer();
        this.declTransformer = new EldaricaDeclTransformer(this, symbolTable);
        this.exprTransformer = new EldaricaExprTransformer(this);
    }

    public Sort toSort(final Type type) {
        return typeTransformer.toSort(type);
    }

    public Utils.PredTermFormula toSymbol(final Decl<?> decl) {
        return declTransformer.toSymbol(decl);
    }

    public Utils.PredTermFormula toTerm(final Expr<?> expr) {
        return exprTransformer.toTerm(expr);
    }
}
