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

import com.microsoft.z3legacy.BoolExpr;
import com.microsoft.z3legacy.Context;
import com.microsoft.z3legacy.FuncInterp;
import com.microsoft.z3legacy.Model;
import com.microsoft.z3legacy.Solver;
import com.microsoft.z3legacy.Sort;
import hu.bme.mit.theta.core.type.arraytype.ArrayExprs;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.inttype.IntExprs;
import java.util.List;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import org.mockito.Mockito;

public final class Z3ModelTest {

    static {
        Z3LegacySolverFactory.getInstance();
    }

    @Test
    public void test() {
        final Context context = new Context();
        final Solver solver = context.mkSimpleSolver();

        final BoolExpr a = context.mkBoolConst("a");
        final BoolExpr b = context.mkBoolConst("b");
        final BoolExpr expr = context.mkOr(a, b);

        solver.add(expr);
        solver.check();
        final Model model = solver.getModel();

        Assertions.assertTrue(model.getConstInterp(a).isTrue());
        Assertions.assertNull(model.getConstInterp(b));

        context.close();
    }

    @Test
    public void constantArrayDefaultsUninterpretedNestedArrayValues() {
        final Context context = new Context();
        try {
            final var rowSort = context.mkArraySort(context.getIntSort(), context.getIntSort());
            final var modeSort = context.mkArraySort(context.getIntSort(), rowSort);
            final var owners =
                    context.mkConst("owners", context.mkArraySort(context.getIntSort(), modeSort));
            final var unspecifiedRow = context.mkConst("unspecified_row", rowSort);
            final var interpretation = context.mkConstArray(context.getIntSort(), unspecifiedRow);
            final Model model = Mockito.mock(Model.class);
            final FuncInterp function = Mockito.mock(FuncInterp.class);
            Mockito.doReturn(function).when(model).getFuncInterp(owners.getFuncDecl());
            Mockito.doReturn(new FuncInterp.Entry[0]).when(function).getEntries();
            Mockito.doReturn(interpretation).when(function).getElse();

            final var transformer =
                    new Z3TermTransformer(new Z3SymbolTable(), new Z3TypeSymbolTable());
            final var actual = transformer.toArrayLitExpr(owners.getFuncDecl(), model, List.of());
            final var rowType = ArrayExprs.Array(IntExprs.Int(), IntExprs.Int());
            final var emptyRow = ArrayExprs.Array(List.of(), IntExprs.Int(0), rowType);
            final var modes =
                    ArrayExprs.Array(
                            List.of(), emptyRow, ArrayExprs.Array(IntExprs.Int(), rowType));
            final var expected =
                    ArrayExprs.Array(
                            List.of(), modes, ArrayExprs.Array(IntExprs.Int(), modes.getType()));
            Assertions.assertEquals(expected, actual);
        } finally {
            context.close();
        }
    }

    @Test
    public void arrayValuedFunctionKeepsItsDomainAsTheOuterIndexType() {
        final Context context = new Context();
        try {
            final var rowSort = context.mkArraySort(context.getIntSort(), context.getIntSort());
            final var function =
                    context.mkFuncDecl(
                            "owners_by_mode", new Sort[] {context.getBoolSort()}, rowSort);
            final var row = context.mkConstArray(context.getIntSort(), context.mkInt(4));
            final Model model = Mockito.mock(Model.class);
            final FuncInterp interpretation = Mockito.mock(FuncInterp.class);
            Mockito.doReturn(interpretation).when(model).getFuncInterp(function);
            Mockito.doReturn(new FuncInterp.Entry[0]).when(interpretation).getEntries();
            Mockito.doReturn(row).when(interpretation).getElse();
            final var transformer =
                    new Z3TermTransformer(new Z3SymbolTable(), new Z3TypeSymbolTable());
            final var actual = transformer.toArrayLitExpr(function, model, List.of());
            final var rowType = ArrayExprs.Array(IntExprs.Int(), IntExprs.Int());
            final var expectedRow = ArrayExprs.Array(List.of(), IntExprs.Int(4), rowType);
            Assertions.assertEquals(
                    ArrayExprs.Array(
                            List.of(), expectedRow, ArrayExprs.Array(BoolExprs.Bool(), rowType)),
                    actual);
        } finally {
            context.close();
        }
    }
}
