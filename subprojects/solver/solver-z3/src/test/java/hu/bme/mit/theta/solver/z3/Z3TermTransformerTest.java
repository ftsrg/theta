/*
 *  Copyright 2026 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.solver.z3;

import static hu.bme.mit.theta.core.type.bvtype.BvExprs.BvType;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.ToBv;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static org.junit.jupiter.api.Assertions.assertEquals;

import com.microsoft.z3.Context;
import org.junit.jupiter.api.Test;

public class Z3TermTransformerTest {

    @Test
    public void testIntToBvRoundtrip() {
        try (final var context = new Context()) {
            final var symbolTable = new Z3SymbolTable();
            final var transformationManager = new Z3TransformationManager(symbolTable, context);
            final var termTransformer = new Z3TermTransformer(symbolTable);

            final var expr = ToBv(Int(14), BvType(4));
            final var term = transformationManager.toTerm(expr);

            assertEquals(expr, termTransformer.toExpr(term));
        }
    }
}
