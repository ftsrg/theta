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
package hu.bme.mit.theta.common.parser;

import static com.google.common.collect.ImmutableList.of;
import static hu.bme.mit.theta.common.parser.SExpr.atom;
import static hu.bme.mit.theta.common.parser.SExpr.list;
import static org.junit.jupiter.api.Assertions.assertEquals;

import java.util.Arrays;
import java.util.Collection;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

public final class SExpTest {

    private static final String A = "A";
    private static final String B = "B";
    private static final String C = "C";
    public Object object;
    public SExpr sexpr;
    public String string;

    public static Collection<Object[]> data() {
        return Arrays.asList(
                new Object[][] {
                    {A, atom(A), A},
                    {of(), list(), "()"},
                    {of(A), list(atom(A)), "(A)"},
                    {of(A, B), list(atom(A), atom(B)), "(A B)"},
                    {of(A, B, C), list(atom(A), atom(B), atom(C)), "(A B C)"},
                    {of(A, of(B, C)), list(atom(A), list(atom(B), atom(C))), "(A (B C))"},
                    {
                        of(A, B, of(C, of(A))),
                        list(atom(A), atom(B), list(atom(C), list(atom(A)))),
                        "(A B (C (A)))"
                    }
                });
    }

    @MethodSource("data")
    @ParameterizedTest
    public void testBuild(Object object, SExpr sexpr, String string) {
        initSExpTest(object, sexpr, string);
        final SExpr actSexpr = SExpr.build(object);
        assertEquals(sexpr, actSexpr);
    }

    @MethodSource("data")
    @ParameterizedTest
    public void testParse(Object object, SExpr sexpr, String string) {
        initSExpTest(object, sexpr, string);
        final SExpr actSexpr = SExpr.parse(string);
        assertEquals(sexpr, actSexpr);
    }

    @MethodSource("data")
    @ParameterizedTest
    public void testToString(Object object, SExpr sexpr, String string) {
        initSExpTest(object, sexpr, string);
        final String actString = sexpr.toString();
        assertEquals(string, actString);
    }

    public void initSExpTest(Object object, SExpr sexpr, String string) {
        this.object = object;
        this.sexpr = sexpr;
        this.string = string;
    }
}
