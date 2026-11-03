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

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.BoolSort;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.FuncInterp;
import com.microsoft.z3.Model;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Sort;
import com.microsoft.z3.Status;
import hu.bme.mit.theta.core.type.arraytype.ArrayExprs;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.inttype.IntExprs;
import java.util.List;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import org.mockito.Mockito;

public final class Z3ModelTest {

    static {
        Z3SolverFactory.getInstance();
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
    public void testFuncInterpEntriesKeepTheirArguments() {
        final Context context = new Context();
        final Solver solver = context.mkSimpleSolver();

        final FuncDecl<BoolSort> f =
                context.mkFuncDecl("f", new Sort[] {context.getIntSort()}, context.getBoolSort());
        solver.add((BoolExpr) f.apply(context.mkInt(1)));
        solver.add(context.mkNot((BoolExpr) f.apply(context.mkInt(2))));
        Assertions.assertEquals(Status.SATISFIABLE, solver.check());

        final BoolExpr body = InterpolationMetadata.interpretation(context, solver.getModel(), f);

        // f(1) and f(2) disagree, so a reconstruction that drops the entries' arguments is wrong.
        Assertions.assertTrue(holdsAt(context, body, 1));
        Assertions.assertFalse(holdsAt(context, body, 2));

        context.close();
    }

    @Test
    public void constantArrayDefaultsUninterpretedNestedArrayValues() {
        try (final Context context = new Context()) {
            final var rowSort = context.mkArraySort(context.getIntSort(), context.getIntSort());
            final var modeSort = context.mkArraySort(context.getBoolSort(), rowSort);
            final var owners =
                    context.mkConst("owners", context.mkArraySort(context.getIntSort(), modeSort));
            final var unspecifiedRow = context.mkConst("unspecified_row", rowSort);
            final var interpretation =
                    context.mkConstArray(
                            context.getIntSort(),
                            context.mkConstArray(context.getBoolSort(), unspecifiedRow));
            final Model model = Mockito.mock(Model.class);
            Mockito.doReturn(interpretation).when(model).getConstInterp(owners.getFuncDecl());

            final var transformer = new Z3TermTransformer(new Z3SymbolTable());
            final var actual = transformer.toArrayLitExpr(owners.getFuncDecl(), model, List.of());
            final var rowType = ArrayExprs.Array(IntExprs.Int(), IntExprs.Int());
            final var emptyRow = ArrayExprs.Array(List.of(), IntExprs.Int(0), rowType);
            final var modes =
                    ArrayExprs.Array(
                            List.of(), emptyRow, ArrayExprs.Array(BoolExprs.Bool(), rowType));
            final var expected =
                    ArrayExprs.Array(
                            List.of(), modes, ArrayExprs.Array(IntExprs.Int(), modes.getType()));
            Assertions.assertEquals(expected, actual);
        }
    }

    @Test
    public void arrayValuedFunctionKeepsItsDomainAsTheOuterIndexType() {
        try (final Context context = new Context()) {
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
            final var transformer = new Z3TermTransformer(new Z3SymbolTable());
            final var actual = transformer.toArrayLitExpr(function, model, List.of());
            final var rowType = ArrayExprs.Array(IntExprs.Int(), IntExprs.Int());
            final var expectedRow = ArrayExprs.Array(List.of(), IntExprs.Int(4), rowType);
            Assertions.assertEquals(
                    ArrayExprs.Array(
                            List.of(), expectedRow, ArrayExprs.Array(BoolExprs.Bool(), rowType)),
                    actual);
        }
    }

    @Test
    public void storesOverAsArrayUseTheFunctionInterpretation() {
        try (final Context context = new Context()) {
            final var assertion =
                    context.parseSMTLIB2String(
                                    "(declare-fun f (Int) Int) (declare-const a (Array Int Int)) "
                                            + "(assert (= a (store (_ as-array f) 7 9)))",
                                    null,
                                    null,
                                    null,
                                    null)[0];
            final var array = assertion.getArgs()[0];
            final var value = assertion.getArgs()[1];
            final var function = value.getArgs()[0].getFuncDecl().getParameters()[0].getFuncDecl();
            final Model model = Mockito.mock(Model.class);
            final FuncInterp interpretation = Mockito.mock(FuncInterp.class);
            Mockito.doReturn(value).when(model).getConstInterp(array.getFuncDecl());
            Mockito.doReturn(interpretation).when(model).getFuncInterp(function);
            Mockito.doReturn(new FuncInterp.Entry[0]).when(interpretation).getEntries();
            Mockito.doReturn(context.mkInt(4)).when(interpretation).getElse();
            final var transformer = new Z3TermTransformer(new Z3SymbolTable());
            final var actual = transformer.toArrayLitExpr(array.getFuncDecl(), model, List.of());
            final var rowType = ArrayExprs.Array(IntExprs.Int(), IntExprs.Int());
            final var expected =
                    ArrayExprs.Array(
                            List.of(
                                    hu.bme.mit.theta.common.Tuple2.of(
                                            IntExprs.Int(7), IntExprs.Int(9))),
                            IntExprs.Int(4),
                            rowType);
            Assertions.assertEquals(expected, actual);
        }
    }

    /** Whether [body], read as the interpretation of a unary predicate, holds at [arg]. */
    private static boolean holdsAt(final Context context, final BoolExpr body, final int arg) {
        final Solver solver = context.mkSimpleSolver();
        solver.add(context.mkNot((BoolExpr) body.substituteVars(new Expr[] {context.mkInt(arg)})));
        return solver.check() == Status.UNSATISFIABLE;
    }
}
