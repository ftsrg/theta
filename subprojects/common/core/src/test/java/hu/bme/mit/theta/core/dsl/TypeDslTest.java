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
package hu.bme.mit.theta.core.dsl;

import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.arraytype.ArrayExprs;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.inttype.IntExprs;
import hu.bme.mit.theta.core.type.rattype.RatExprs;
import java.util.Arrays;
import java.util.Collection;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

public class TypeDslTest {
    public String actual;
    public Type expected;

    public static Collection<Object[]> data() {
        return Arrays.asList(
                new Object[][] {
                    {"int", IntExprs.Int()},
                    {"rat", RatExprs.Rat()},
                    {"bool", BoolExprs.Bool()},
                    {"[int] -> bool", ArrayExprs.Array(IntExprs.Int(), BoolExprs.Bool())},
                    {"[bool] -> rat", ArrayExprs.Array(BoolExprs.Bool(), RatExprs.Rat())},
                    {
                        "[bool] -> [int] -> rat",
                        ArrayExprs.Array(
                                BoolExprs.Bool(), ArrayExprs.Array(IntExprs.Int(), RatExprs.Rat()))
                    },
                    {
                        "[[bool] -> int] -> rat",
                        ArrayExprs.Array(
                                ArrayExprs.Array(BoolExprs.Bool(), IntExprs.Int()), RatExprs.Rat())
                    },
                });
    }

    @MethodSource("data")
    @ParameterizedTest
    public void test(String actual, Type expected) {
        initTypeDslTest(actual, expected);
        final CoreDslManager manager = new CoreDslManager();
        Assertions.assertEquals(expected, manager.parseType(actual));
    }

    public void initTypeDslTest(String actual, Type expected) {
        this.actual = actual;
        this.expected = expected;
    }
}
