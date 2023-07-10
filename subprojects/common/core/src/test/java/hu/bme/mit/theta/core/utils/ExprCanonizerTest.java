/*
 *  Copyright 2023 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntExprs;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.type.rattype.RatExprs;
import hu.bme.mit.theta.core.type.rattype.RatType;
import org.junit.Test;
import org.junit.experimental.runners.Enclosed;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;

import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.anytype.Exprs.Ite;
import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.*;
import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Read;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.*;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.*;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.*;
import static hu.bme.mit.theta.core.utils.ExprCanonizer.canonize;
import static org.junit.Assert.assertEquals;

@RunWith(Enclosed.class)
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

    @RunWith(Enclosed.class)
    public static class CommutativeBinaryTest {

        @RunWith(Parameterized.class)
        public static class CommutativeBinaryBoolTest {

            @Parameterized.Parameter(value = 0)
            public Expr<BoolType> a1;

            @Parameterized.Parameter(value = 1)
            public Expr<BoolType> b1;

            @Parameterized.Parameter(value = 2)
            public Expr<BoolType> a2;

            @Parameterized.Parameter(value = 3)
            public Expr<BoolType> b2;

            @Parameterized.Parameters(name = "{index}: {0}, {1}, {2}, {3}")
            public static Collection<Object[]> data() {
                return Arrays.asList(new Object[][]{

                        {x, y,
                                y, x},

                        {x, y,
                                x, y},

                        {x, True(),
                                x, True()},

                        {x, True(),
                                True(), x},

                });
            }

            @Test
            public void testIff() {
                assertEquals(canonize(Iff(a1, b1)), canonize(Iff(a2, b2)));
            }

            @Test
            public void testXor() {
                assertEquals(canonize(Xor(a1, b1)), canonize(Xor(a2, b2)));
            }

        }

        @RunWith(Parameterized.class)
        public static class CommutativeBinaryIntTest {

            @Parameterized.Parameter(value = 0)
            public Expr<IntType> a1;

            @Parameterized.Parameter(value = 1)
            public Expr<IntType> b1;

            @Parameterized.Parameter(value = 2)
            public Expr<IntType> a2;

            @Parameterized.Parameter(value = 3)
            public Expr<IntType> b2;

            @Parameterized.Parameters(name = "{index}: {0}, {1}, {2}, {3}")
            public static Collection<Object[]> data() {
                return Arrays.asList(new Object[][]{

                        {a, b,
                                b, a},

                        {a, b,
                                a, b},

                        {a, Int(1),
                                a, Int(1)},

                        {a, Int(1),
                                Int(1), a},

                });
            }

            @Test
            public void testIntEq() {
                assertEquals(canonize(IntExprs.Eq(a1, b1)), canonize(IntExprs.Eq(a2, b2)));
            }

            @Test
            public void testIntNeq() {
                assertEquals(canonize(IntExprs.Neq(a1, b1)), canonize(IntExprs.Neq(a2, b2)));
            }

        }

        @RunWith(Parameterized.class)
        public static class CommutativeBinaryRatTest {

            @Parameterized.Parameter(value = 0)
            public Expr<RatType> a1;

            @Parameterized.Parameter(value = 1)
            public Expr<RatType> b1;

            @Parameterized.Parameter(value = 2)
            public Expr<RatType> a2;

            @Parameterized.Parameter(value = 3)
            public Expr<RatType> b2;

            @Parameterized.Parameters(name = "{index}: {0}, {1}, {2}, {3}")
            public static Collection<Object[]> data() {
                return Arrays.asList(new Object[][]{

                        {d, d,
                                d, d},

                        {d, Rat(1, 2),
                                Rat(1, 2), d},


                });
            }

            @Test
            public void testRatEq() {
                assertEquals(canonize(RatExprs.Eq(a1, b1)), canonize(RatExprs.Eq(a2, b2)));
            }

            @Test
            public void testRatNeq() {
                assertEquals(canonize(RatExprs.Neq(a1, b1)), canonize(RatExprs.Neq(a2, b2)));
            }


        }

    }

    @RunWith(Enclosed.class)
    public static class CommutativeMultiaryTest {

        @RunWith(Parameterized.class)
        public static class CommutativeMultiaryBoolTest {

            @Parameterized.Parameter(value = 0)
            public Expr<BoolType> a1;

            @Parameterized.Parameter(value = 1)
            public Expr<BoolType> b1;

            @Parameterized.Parameter(value = 2)
            public Expr<BoolType> c1;

            @Parameterized.Parameter(value = 3)
            public Expr<BoolType> a2;

            @Parameterized.Parameter(value = 4)
            public Expr<BoolType> b2;

            @Parameterized.Parameter(value = 5)
            public Expr<BoolType> c2;

            @Parameterized.Parameters(name = "{index}: {0}, {1}, {2}, {3}, {4}, {5}")
            public static Collection<Object[]> data() {
                return Arrays.asList(new Object[][]{

                        {x, y, z,
                                y, x, z},

                        {x, y, z,
                                x, y, z},

                        {x, True(), x,
                                x, x, True()},

                        {x, True(), True(),
                                True(), x, True()},


                });
            }

            @Test
            public void testAnd() {
                assertEquals(canonize(And(a1, b1, c1)), canonize(And(a2, b2, c2)));
            }

            @Test
            public void testOr() {
                assertEquals(canonize(Or(a1, b1, c1)), canonize(Or(a2, b2, c2)));
            }

        }

        @RunWith(Parameterized.class)
        public static class CommutativeMultiaryIntTest {

            @Parameterized.Parameter(value = 0)
            public Expr<IntType> a1;

            @Parameterized.Parameter(value = 1)
            public Expr<IntType> b1;

            @Parameterized.Parameter(value = 2)
            public Expr<IntType> c1;

            @Parameterized.Parameter(value = 3)
            public Expr<IntType> a2;

            @Parameterized.Parameter(value = 4)
            public Expr<IntType> b2;

            @Parameterized.Parameter(value = 5)
            public Expr<IntType> c2;

            @Parameterized.Parameters(name = "{index}: {0}, {1}, {2}, {3}, {4}, {5}")
            public static Collection<Object[]> data() {
                return Arrays.asList(new Object[][]{

                        {a, b, b,
                                b, a, b},

                        {a, b, a,
                                a, b, a},

                        {a, Int(1), Int(2),
                                Int(2), a, Int(1)},

                        {a, Int(1), b,
                                b, Int(1), a},

                });
            }

            @Test
            public void testIntAdd() {
                assertEquals(canonize(IntExprs.Add(a1, b1, c1)),
                        canonize(IntExprs.Add(a2, b2, c2)));
            }

            @Test
            public void testIntMul() {
                assertEquals(canonize(IntExprs.Mul(a1, b1, c1)),
                        canonize(IntExprs.Mul(a2, b2, c2)));
            }

        }

        @RunWith(Parameterized.class)
        public static class CommutativeMultiaryRatTest {

            @Parameterized.Parameter(value = 0)
            public Expr<RatType> a1;

            @Parameterized.Parameter(value = 1)
            public Expr<RatType> b1;

            @Parameterized.Parameter(value = 2)
            public Expr<RatType> c1;

            @Parameterized.Parameter(value = 3)
            public Expr<RatType> a2;

            @Parameterized.Parameter(value = 4)
            public Expr<RatType> b2;

            @Parameterized.Parameter(value = 5)
            public Expr<RatType> c2;

            @Parameterized.Parameters(name = "{index}: {0}, {1}, {2}, {3}, {4}, {5}")
            public static Collection<Object[]> data() {
                return Arrays.asList(new Object[][]{

                        {d, d, d,
                                d, d, d},

                        {d, Rat(1, 2), Rat(1, 2),
                                Rat(1, 2), Rat(1, 2), d},


                });
            }

            @Test
            public void testRatAdd() {
                assertEquals(canonize(RatExprs.Add(a1, b1, c1)),
                        canonize(RatExprs.Add(a2, b2, c2)));
            }

            @Test
            public void testRatMul() {
                assertEquals(canonize(RatExprs.Mul(a1, b1, c1)),
                        canonize(RatExprs.Mul(a2, b2, c2)));
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
            assertEquals(canonize(RatExprs.Geq(Rat(8, 3), Rat(2, 1))),
                    canonize(RatExprs.Geq(Rat(8, 3), Rat(2, 1))));
            assertEquals(canonize(RatExprs.Leq(Rat(2, 1), Rat(8, 3))),
                    canonize(RatExprs.Geq(Rat(8, 3), Rat(2, 1))));
            assertEquals(canonize(RatExprs.Geq(Rat(8, 4), d)),
                    canonize(RatExprs.Geq(Rat(8, 4), d)));
            assertEquals(canonize(RatExprs.Leq(Rat(2, 1), d)),
                    canonize(RatExprs.Geq(d, Rat(2, 1))));
        }

        @Test
        public void testRatGt() {
            assertEquals(canonize(RatExprs.Gt(Rat(8, 3), Rat(2, 1))),
                    canonize(RatExprs.Gt(Rat(8, 3), Rat(2, 1))));
            assertEquals(canonize(RatExprs.Lt(Rat(2, 1), Rat(8, 3))),
                    canonize(RatExprs.Gt(Rat(8, 3), Rat(2, 1))));
            assertEquals(canonize(RatExprs.Gt(Rat(8, 4), d)), canonize(RatExprs.Gt(Rat(8, 4), d)));
            assertEquals(canonize(RatExprs.Lt(Rat(2, 1), d)), canonize(RatExprs.Gt(d, Rat(2, 1))));
        }

        @Test
        public void testRatLeq() {
            assertEquals(canonize(RatExprs.Leq(Rat(8, 3), Rat(2, 1))),
                    canonize(RatExprs.Leq(Rat(8, 3), Rat(2, 1))));
            assertEquals(canonize(RatExprs.Leq(Rat(2, 1), Rat(8, 3))),
                    canonize(RatExprs.Geq(Rat(8, 3), Rat(2, 1))));
            assertEquals(canonize(RatExprs.Leq(Rat(8, 4), d)),
                    canonize(RatExprs.Leq(Rat(8, 4), d)));
            assertEquals(canonize(RatExprs.Leq(Rat(2, 1), d)),
                    canonize(RatExprs.Geq(d, Rat(2, 1))));
        }

        @Test
        public void testRatLt() {
            assertEquals(canonize(RatExprs.Lt(Rat(8, 3), Rat(2, 1))),
                    canonize(RatExprs.Lt(Rat(8, 3), Rat(2, 1))));
            assertEquals(canonize(RatExprs.Lt(Rat(2, 1), Rat(8, 3))),
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
            assertEquals(Ite(True(), Ite(True(), Ite(True(), a, b), b), b),
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
            assertEquals(canonize(Iff(Or(False(), x), And(True(), x))),
                    canonize(Iff(And(x, True()), Or(x, False()))));
        }

    }

}
