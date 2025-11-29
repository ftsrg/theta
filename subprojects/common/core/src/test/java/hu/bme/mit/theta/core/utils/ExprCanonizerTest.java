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
package hu.bme.mit.theta.core.utils;

import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.anytype.Exprs.Ite;
import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.*;
import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Read;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.*;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.*;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.*;
import static hu.bme.mit.theta.core.utils.ExprCanonizer.canonize;
import static org.junit.jupiter.api.Assertions.assertEquals;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntExprs;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.type.rattype.RatExprs;
import hu.bme.mit.theta.core.type.rattype.RatType;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

public class ExprCanonizerTest {

    private static final ConstDecl<BoolType> cx = Const("x", Bool());
    private static final ConstDecl<BoolType> cy = Const("y", Bool());
    private static final ConstDecl<BoolType> cz = Const("z", Bool());
    private static final ConstDecl<IntType> ca = Const("a", Int());
    private static final ConstDecl<IntType> cb = Const("b", Int());
    private static final ConstDecl<IntType> cc = Const("c", Int());
    private static final ConstDecl<RatType> cd = Const("d", Rat());

    private static final Expr<BoolType> x = cx.getRef();
    private static final Expr<BoolType> y = cy.getRef();
    private static final Expr<BoolType> z = cz.getRef();
    private static final Expr<IntType> a = ca.getRef();
    private static final Expr<IntType> b = cb.getRef();
    private static final Expr<IntType> c = cc.getRef();
    private static final Expr<RatType> d = cd.getRef();

    public static class CommutativeBinaryTest {

        public static class CommutativeBinaryBoolTest {
            public Expr<BoolType> a1;
            public Expr<BoolType> b1;
            public Expr<BoolType> a2;
            public Expr<BoolType> b2;

            public static Collection<Object[]> data() {
                return Arrays.asList(
                        new Object[][] {
                            {x, y, y, x},
                            {x, y, x, y},
                            {x, True(), x, True()},
                            {x, True(), True(), x},
                        });
            }

            @MethodSource("data")
            @ParameterizedTest(name = "{index}: {0}, {1}, {2}, {3}")
            public void testIff(
                    Expr<BoolType> a1, Expr<BoolType> b1, Expr<BoolType> a2, Expr<BoolType> b2) {
                initCommutativeBinaryBoolTest(a1, b1, a2, b2);
                assertEquals(canonize(Iff(a1, b1)), canonize(Iff(a2, b2)));
            }

            @MethodSource("data")
            @ParameterizedTest(name = "{index}: {0}, {1}, {2}, {3}")
            public void testXor(
                    Expr<BoolType> a1, Expr<BoolType> b1, Expr<BoolType> a2, Expr<BoolType> b2) {
                initCommutativeBinaryBoolTest(a1, b1, a2, b2);
                assertEquals(canonize(Xor(a1, b1)), canonize(Xor(a2, b2)));
            }

            public void initCommutativeBinaryBoolTest(
                    Expr<BoolType> a1, Expr<BoolType> b1, Expr<BoolType> a2, Expr<BoolType> b2) {
                this.a1 = a1;
                this.b1 = b1;
                this.a2 = a2;
                this.b2 = b2;
            }
        }

        public static class CommutativeBinaryIntTest {

            public Expr<IntType> a1;

            public Expr<IntType> b1;

            public Expr<IntType> a2;

            public Expr<IntType> b2;

            public static Collection<Object[]> data() {
                return Arrays.asList(
                        new Object[][] {
                            {a, b, b, a},
                            {a, b, a, b},
                            {a, Int(1), a, Int(1)},
                            {a, Int(1), Int(1), a},
                        });
            }

            @MethodSource("data")
            @ParameterizedTest(name = "{index}: {0}, {1}, {2}, {3}")
            public void testIntEq(
                    Expr<IntType> a1, Expr<IntType> b1, Expr<IntType> a2, Expr<IntType> b2) {
                initCommutativeBinaryIntTest(a1, b1, a2, b2);
                assertEquals(canonize(IntExprs.Eq(a1, b1)), canonize(IntExprs.Eq(a2, b2)));
            }

            @MethodSource("data")
            @ParameterizedTest(name = "{index}: {0}, {1}, {2}, {3}")
            public void testIntNeq(
                    Expr<IntType> a1, Expr<IntType> b1, Expr<IntType> a2, Expr<IntType> b2) {
                initCommutativeBinaryIntTest(a1, b1, a2, b2);
                assertEquals(canonize(IntExprs.Neq(a1, b1)), canonize(IntExprs.Neq(a2, b2)));
            }

            public void initCommutativeBinaryIntTest(
                    Expr<IntType> a1, Expr<IntType> b1, Expr<IntType> a2, Expr<IntType> b2) {
                this.a1 = a1;
                this.b1 = b1;
                this.a2 = a2;
                this.b2 = b2;
            }
        }

        public static class CommutativeBinaryRatTest {

            public Expr<RatType> a1;

            public Expr<RatType> b1;

            public Expr<RatType> a2;

            public Expr<RatType> b2;

            public static Collection<Object[]> data() {
                return Arrays.asList(
                        new Object[][] {
                            {d, d, d, d},
                            {d, Rat(1, 2), Rat(1, 2), d},
                        });
            }

            @MethodSource("data")
            @ParameterizedTest(name = "{index}: {0}, {1}, {2}, {3}")
            public void testRatEq(
                    Expr<RatType> a1, Expr<RatType> b1, Expr<RatType> a2, Expr<RatType> b2) {
                initCommutativeBinaryRatTest(a1, b1, a2, b2);
                assertEquals(canonize(RatExprs.Eq(a1, b1)), canonize(RatExprs.Eq(a2, b2)));
            }

            @MethodSource("data")
            @ParameterizedTest(name = "{index}: {0}, {1}, {2}, {3}")
            public void testRatNeq(
                    Expr<RatType> a1, Expr<RatType> b1, Expr<RatType> a2, Expr<RatType> b2) {
                initCommutativeBinaryRatTest(a1, b1, a2, b2);
                assertEquals(canonize(RatExprs.Neq(a1, b1)), canonize(RatExprs.Neq(a2, b2)));
            }

            public void initCommutativeBinaryRatTest(
                    Expr<RatType> a1, Expr<RatType> b1, Expr<RatType> a2, Expr<RatType> b2) {
                this.a1 = a1;
                this.b1 = b1;
                this.a2 = a2;
                this.b2 = b2;
            }
        }
    }

    public static class CommutativeMultiaryTest {

        public static class CommutativeMultiaryBoolTest {

            public Expr<BoolType> a1;

            public Expr<BoolType> b1;

            public Expr<BoolType> c1;

            public Expr<BoolType> a2;

            public Expr<BoolType> b2;

            public Expr<BoolType> c2;

            public static Collection<Object[]> data() {
                return Arrays.asList(
                        new Object[][] {
                            {x, y, z, y, x, z},
                            {x, y, z, x, y, z},
                            {x, True(), x, x, x, True()},
                            {x, True(), True(), True(), x, True()},
                        });
            }

            @MethodSource("data")
            @ParameterizedTest(name = "{index}: {0}, {1}, {2}, {3}, {4}, {5}")
            public void testAnd(
                    Expr<BoolType> a1,
                    Expr<BoolType> b1,
                    Expr<BoolType> c1,
                    Expr<BoolType> a2,
                    Expr<BoolType> b2,
                    Expr<BoolType> c2) {
                initCommutativeMultiaryBoolTest(a1, b1, c1, a2, b2, c2);
                assertEquals(canonize(And(a1, b1, c1)), canonize(And(a2, b2, c2)));
            }

            @MethodSource("data")
            @ParameterizedTest(name = "{index}: {0}, {1}, {2}, {3}, {4}, {5}")
            public void testOr(
                    Expr<BoolType> a1,
                    Expr<BoolType> b1,
                    Expr<BoolType> c1,
                    Expr<BoolType> a2,
                    Expr<BoolType> b2,
                    Expr<BoolType> c2) {
                initCommutativeMultiaryBoolTest(a1, b1, c1, a2, b2, c2);
                assertEquals(canonize(Or(a1, b1, c1)), canonize(Or(a2, b2, c2)));
            }

            public void initCommutativeMultiaryBoolTest(
                    Expr<BoolType> a1,
                    Expr<BoolType> b1,
                    Expr<BoolType> c1,
                    Expr<BoolType> a2,
                    Expr<BoolType> b2,
                    Expr<BoolType> c2) {
                this.a1 = a1;
                this.b1 = b1;
                this.c1 = c1;
                this.a2 = a2;
                this.b2 = b2;
                this.c2 = c2;
            }
        }

        public static class CommutativeMultiaryIntTest {

            public Expr<IntType> a1;

            public Expr<IntType> b1;

            public Expr<IntType> c1;

            public Expr<IntType> a2;

            public Expr<IntType> b2;

            public Expr<IntType> c2;

            public static Collection<Object[]> data() {
                return Arrays.asList(
                        new Object[][] {
                            {a, b, b, b, a, b},
                            {a, b, a, a, b, a},
                            {a, Int(1), Int(2), Int(2), a, Int(1)},
                            {a, Int(1), b, b, Int(1), a},
                        });
            }

            @MethodSource("data")
            @ParameterizedTest(name = "{index}: {0}, {1}, {2}, {3}, {4}, {5}")
            public void testIntAdd(
                    Expr<IntType> a1,
                    Expr<IntType> b1,
                    Expr<IntType> c1,
                    Expr<IntType> a2,
                    Expr<IntType> b2,
                    Expr<IntType> c2) {
                initCommutativeMultiaryIntTest(a1, b1, c1, a2, b2, c2);
                assertEquals(
                        canonize(IntExprs.Add(a1, b1, c1)), canonize(IntExprs.Add(a2, b2, c2)));
            }

            @MethodSource("data")
            @ParameterizedTest(name = "{index}: {0}, {1}, {2}, {3}, {4}, {5}")
            public void testIntMul(
                    Expr<IntType> a1,
                    Expr<IntType> b1,
                    Expr<IntType> c1,
                    Expr<IntType> a2,
                    Expr<IntType> b2,
                    Expr<IntType> c2) {
                initCommutativeMultiaryIntTest(a1, b1, c1, a2, b2, c2);
                assertEquals(
                        canonize(IntExprs.Mul(a1, b1, c1)), canonize(IntExprs.Mul(a2, b2, c2)));
            }

            public void initCommutativeMultiaryIntTest(
                    Expr<IntType> a1,
                    Expr<IntType> b1,
                    Expr<IntType> c1,
                    Expr<IntType> a2,
                    Expr<IntType> b2,
                    Expr<IntType> c2) {
                this.a1 = a1;
                this.b1 = b1;
                this.c1 = c1;
                this.a2 = a2;
                this.b2 = b2;
                this.c2 = c2;
            }
        }

        public static class CommutativeMultiaryRatTest {

            public Expr<RatType> a1;

            public Expr<RatType> b1;

            public Expr<RatType> c1;

            public Expr<RatType> a2;

            public Expr<RatType> b2;

            public Expr<RatType> c2;

            public static Collection<Object[]> data() {
                return Arrays.asList(
                        new Object[][] {
                            {d, d, d, d, d, d},
                            {d, Rat(1, 2), Rat(1, 2), Rat(1, 2), Rat(1, 2), d},
                        });
            }

            @MethodSource("data")
            @ParameterizedTest(name = "{index}: {0}, {1}, {2}, {3}, {4}, {5}")
            public void testRatAdd(
                    Expr<RatType> a1,
                    Expr<RatType> b1,
                    Expr<RatType> c1,
                    Expr<RatType> a2,
                    Expr<RatType> b2,
                    Expr<RatType> c2) {
                initCommutativeMultiaryRatTest(a1, b1, c1, a2, b2, c2);
                assertEquals(
                        canonize(RatExprs.Add(a1, b1, c1)), canonize(RatExprs.Add(a2, b2, c2)));
            }

            @MethodSource("data")
            @ParameterizedTest(name = "{index}: {0}, {1}, {2}, {3}, {4}, {5}")
            public void testRatMul(
                    Expr<RatType> a1,
                    Expr<RatType> b1,
                    Expr<RatType> c1,
                    Expr<RatType> a2,
                    Expr<RatType> b2,
                    Expr<RatType> c2) {
                initCommutativeMultiaryRatTest(a1, b1, c1, a2, b2, c2);
                assertEquals(
                        canonize(RatExprs.Mul(a1, b1, c1)), canonize(RatExprs.Mul(a2, b2, c2)));
            }

            public void initCommutativeMultiaryRatTest(
                    Expr<RatType> a1,
                    Expr<RatType> b1,
                    Expr<RatType> c1,
                    Expr<RatType> a2,
                    Expr<RatType> b2,
                    Expr<RatType> c2) {
                this.a1 = a1;
                this.b1 = b1;
                this.c1 = c1;
                this.a2 = a2;
                this.b2 = b2;
                this.c2 = c2;
            }
        }
    }

    public static class NonCommutativeTest {

        // Boolean

        @Test
        public void testNot() {
            assertEquals(Not(True()), canonize(Not(True())));
            assertEquals(Not(x), canonize(Not(x)));
        }

        @Test
        public void testImply() {
            assertEquals(Imply(False(), x), canonize(Imply(False(), x)));
            assertEquals(Imply(True(), x), canonize(Imply(True(), x)));
        }

        // Rational

        @Test
        public void testRatSub() {
            assertEquals(Sub(Rat(3, 4), Rat(1, 2)), canonize(Sub(Rat(3, 4), Rat(1, 2))));
            assertEquals(Sub(Rat(3, 4), Rat(1, 1)), canonize(Sub(Rat(3, 4), Rat(1, 1))));
        }

        @Test
        public void testRatNeg() {
            assertEquals(Neg(Neg(Neg(Neg(Rat(1, 2))))), canonize(Neg(Neg(Neg(Neg(Rat(1, 2)))))));
            assertEquals(Neg(Rat(1, 2)), canonize(Neg(Rat(1, 2))));
        }

        @Test
        public void testRatDiv() {
            assertEquals(Div(Rat(2, 3), Rat(3, 4)), canonize(Div(Rat(2, 3), Rat(3, 4))));
            assertEquals(Div(Rat(2, 3), d), canonize(Div(Rat(2, 3), d)));
        }

        @Test
        public void testRatGeq() {
            assertEquals(
                    canonize(RatExprs.Geq(Rat(8, 3), Rat(2, 1))),
                    canonize(RatExprs.Geq(Rat(8, 3), Rat(2, 1))));
            assertEquals(
                    canonize(RatExprs.Leq(Rat(2, 1), Rat(8, 3))),
                    canonize(RatExprs.Geq(Rat(8, 3), Rat(2, 1))));
            assertEquals(
                    canonize(RatExprs.Geq(Rat(8, 4), d)), canonize(RatExprs.Geq(Rat(8, 4), d)));
            assertEquals(
                    canonize(RatExprs.Leq(Rat(2, 1), d)), canonize(RatExprs.Geq(d, Rat(2, 1))));
        }

        @Test
        public void testRatGt() {
            assertEquals(
                    canonize(RatExprs.Gt(Rat(8, 3), Rat(2, 1))),
                    canonize(RatExprs.Gt(Rat(8, 3), Rat(2, 1))));
            assertEquals(
                    canonize(RatExprs.Lt(Rat(2, 1), Rat(8, 3))),
                    canonize(RatExprs.Gt(Rat(8, 3), Rat(2, 1))));
            assertEquals(canonize(RatExprs.Gt(Rat(8, 4), d)), canonize(RatExprs.Gt(Rat(8, 4), d)));
            assertEquals(canonize(RatExprs.Lt(Rat(2, 1), d)), canonize(RatExprs.Gt(d, Rat(2, 1))));
        }

        @Test
        public void testRatLeq() {
            assertEquals(
                    canonize(RatExprs.Leq(Rat(8, 3), Rat(2, 1))),
                    canonize(RatExprs.Leq(Rat(8, 3), Rat(2, 1))));
            assertEquals(
                    canonize(RatExprs.Leq(Rat(2, 1), Rat(8, 3))),
                    canonize(RatExprs.Geq(Rat(8, 3), Rat(2, 1))));
            assertEquals(
                    canonize(RatExprs.Leq(Rat(8, 4), d)), canonize(RatExprs.Leq(Rat(8, 4), d)));
            assertEquals(
                    canonize(RatExprs.Leq(Rat(2, 1), d)), canonize(RatExprs.Geq(d, Rat(2, 1))));
        }

        @Test
        public void testRatLt() {
            assertEquals(
                    canonize(RatExprs.Lt(Rat(8, 3), Rat(2, 1))),
                    canonize(RatExprs.Lt(Rat(8, 3), Rat(2, 1))));
            assertEquals(
                    canonize(RatExprs.Lt(Rat(2, 1), Rat(8, 3))),
                    canonize(RatExprs.Gt(Rat(8, 3), Rat(2, 1))));
            assertEquals(canonize(RatExprs.Lt(Rat(8, 4), d)), canonize(RatExprs.Lt(Rat(8, 4), d)));
            assertEquals(canonize(RatExprs.Lt(Rat(2, 1), d)), canonize(RatExprs.Gt(d, Rat(2, 1))));
        }

        // Integer

        @Test
        public void testIntToRat() {
            for (int i = -50; i < 50; i++) {
                assertEquals(ToRat(Int(i)), canonize(ToRat(Int(i))));
            }
        }

        @Test
        public void testIntSub() {
            assertEquals(Sub(Int(7), Int(8)), canonize(Sub(Int(7), Int(8))));
            assertEquals(Sub(a, Int(2)), canonize(Sub(a, Int(2))));
        }

        @Test
        public void testIntDiv() {
            assertEquals(Div(Int(1), Int(2)), canonize(Div(Int(1), Int(2))));
            assertEquals(Div(Int(3), Int(2)), canonize(Div(Int(3), Int(2))));
            assertEquals(Div(Int(0), a), canonize(Div(Int(0), a)));
        }

        @Test
        public void testMod() {
            assertEquals(Mod(Int(6), Int(5)), canonize(Mod(Int(6), Int(5))));
            assertEquals(Mod(Int(3), a), canonize(Mod(Int(3), a)));
        }

        @Test
        public void testIntGeq() {
            assertEquals(canonize(Geq(Int(3), Int(4))), canonize(Geq(Int(3), Int(4))));
            assertEquals(canonize(Geq(Int(3), Int(4))), canonize(Leq(Int(4), Int(3))));
            assertEquals(canonize(Geq(a, Int(4))), canonize(Geq(a, Int(4))));
            assertEquals(canonize(Geq(Int(3), a)), canonize(Leq(a, Int(3))));
        }

        @Test
        public void testIntGt() {
            assertEquals(canonize(Gt(Int(3), Int(4))), canonize(Gt(Int(3), Int(4))));
            assertEquals(canonize(Gt(Int(3), Int(4))), canonize(Lt(Int(4), Int(3))));
            assertEquals(canonize(Gt(a, Int(4))), canonize(Gt(a, Int(4))));
            assertEquals(canonize(Gt(Int(3), a)), canonize(Lt(a, Int(3))));
        }

        @Test
        public void testIntLeq() {
            assertEquals(canonize(Leq(Int(3), Int(4))), canonize(Leq(Int(3), Int(4))));
            assertEquals(canonize(Geq(Int(3), Int(4))), canonize(Leq(Int(4), Int(3))));
            assertEquals(canonize(Leq(a, Int(4))), canonize(Leq(a, Int(4))));
            assertEquals(canonize(Geq(Int(3), a)), canonize(Leq(a, Int(3))));
        }

        @Test
        public void testIntLt() {
            assertEquals(canonize(Lt(Int(3), Int(4))), canonize(Lt(Int(3), Int(4))));
            assertEquals(canonize(Gt(Int(3), Int(4))), canonize(Lt(Int(4), Int(3))));
            assertEquals(canonize(Lt(a, Int(4))), canonize(Lt(a, Int(4))));
            assertEquals(canonize(Gt(Int(3), a)), canonize(Lt(a, Int(3))));
        }

        // Others

        @Test
        public void testRef() {
            assertEquals(a, canonize(a));
        }

        @Test
        public void testIte() {
            assertEquals(Ite(True(), a, b), canonize(Ite(True(), a, b)));
            assertEquals(Ite(False(), a, b), canonize(Ite(False(), a, b)));
            assertEquals(
                    Ite(True(), Ite(True(), Ite(True(), a, b), b), b),
                    canonize(Ite(True(), Ite(True(), Ite(True(), a, b), b), b)));
        }

        // Array
        @Test
        public void testArrayRead() {
            var elems = new ArrayList<Tuple2<? extends Expr<IntType>, ? extends Expr<IntType>>>();
            elems.add(Tuple2.of(Int(0), Int(1)));
            elems.add(Tuple2.of(Int(1), Int(2)));
            var arr = Array(elems, Int(100), Array(Int(), Int()));
            assertEquals(Read(arr, Int(0)), canonize(Read(arr, Int(0))));
            assertEquals(Read(arr, a), canonize(Read(arr, a)));
        }

        @Test
        public void testArrayWrite() {
            var elems = new ArrayList<Tuple2<? extends Expr<IntType>, ? extends Expr<IntType>>>();
            elems.add(Tuple2.of(Int(0), Int(1)));
            var arr = Array(elems, Int(100), Array(Int(), Int()));
            assertEquals(Write(arr, Int(5), Int(6)), canonize(Write(arr, Int(5), Int(6))));
            assertEquals(Write(arr, b, a), canonize(Write(arr, b, a)));
        }

        @Test
        public void testComplex() {
            assertEquals(
                    canonize(Iff(Or(False(), x), And(True(), x))),
                    canonize(Iff(And(x, True()), Or(x, False()))));
        }
    }
}
