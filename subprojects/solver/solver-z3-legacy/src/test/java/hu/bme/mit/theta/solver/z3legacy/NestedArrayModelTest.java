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
package hu.bme.mit.theta.solver.z3legacy;

import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neq;
import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Array;
import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Read;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static org.junit.jupiter.api.Assertions.assertTrue;

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.solver.Solver;
import java.util.Optional;
import org.junit.jupiter.api.Test;

/**
 * The XCFA memory model is a two-dimensional array -- {@code arrays[base][offset]} -- so a model for
 * it has array-valued entries, and a byte-addressed union is the thing that fills such an array
 * cell-by-cell. Extracting one used to throw a bare {@code NullPointerException}: {@code
 * createEntryExprs} / {@code toArrayLitExpr} put a null into {@code Tuple2.of(args, value)} whenever a
 * nested array term Z3 left uninterpreted transformed to null. These are smoke tests over that
 * extraction path; the exact production crash is reproduced end to end (a counterexample over a plain
 * {@code unsigned char[16]}, which turned into a NullPointerException before the fix and into a clean
 * Unsafe verdict after), since the precise Z3 model shape that trips it is hard to force through the
 * bare solver API.
 */
public final class NestedArrayModelTest {

    private final ArrayType<IntType, IntType> innerType = Array(Int(), Int());

    private void assertMemoryModelExtractable(
            final ConstDecl<ArrayType<IntType, ArrayType<IntType, IntType>>> memory,
            final Solver solver) {
        assertTrue(solver.check().isSat());
        final Valuation model = solver.getModel();
        final Optional<LitExpr<ArrayType<IntType, ArrayType<IntType, IntType>>>> value =
                model.eval(memory);
        assertTrue(value.isPresent(), "the nested-array model must be extractable, not crash");
    }

    @Test
    public void aConstrainedCellExtracts() {
        final ConstDecl<ArrayType<IntType, ArrayType<IntType, IntType>>> memory =
                Const("mem_cell", Array(Int(), innerType));
        final Solver solver = Z3LegacySolverFactory.getInstance().createSolver();
        solver.add(Eq(Read(Read(memory.getRef(), Int(1)), Int(2)), Int(7)));
        assertMemoryModelExtractable(memory, solver);
    }

    @Test
    public void distinctRowsWithUnconstrainedInnerArraysExtract() {
        final ConstDecl<ArrayType<IntType, ArrayType<IntType, IntType>>> memory =
                Const("mem_rows", Array(Int(), innerType));
        final Solver solver = Z3LegacySolverFactory.getInstance().createSolver();
        // Two outer rows must differ while no inner cell is pinned -- the shape most likely to leave
        // an inner array uninterpreted, whose value transforms to null.
        solver.add(Neq(Read(memory.getRef(), Int(1)), Read(memory.getRef(), Int(2))));
        assertMemoryModelExtractable(memory, solver);
    }
}
