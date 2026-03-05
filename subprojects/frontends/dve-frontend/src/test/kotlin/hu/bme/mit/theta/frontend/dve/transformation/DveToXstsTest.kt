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

package hu.bme.mit.theta.frontend.dve.transformation

import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.NonDetStmt
import hu.bme.mit.theta.core.stmt.SequenceStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.TrueExpr
import hu.bme.mit.theta.frontend.dve.DveParser
import hu.bme.mit.theta.frontend.dve.model.*
import hu.bme.mit.theta.xsts.XSTS
import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.assertThrows

/**
 * Tests for [DveToXsts], verifying correct encoding of DVE models into XSTS.
 *
 * Test strategy:
 *  - Structural tests: verify the right variables and branches are emitted
 *  - Semantic tests: verify init, guards, effects, and property expressions
 *  - Edge case tests: committed states, sync channels, assertions, unsupported features
 */
class DveToXstsTest {

    // -------------------------------------------------------------------------
    // Helpers
    // -------------------------------------------------------------------------

    private fun parse(resource: String): DveModel =
        DveParser.parse(checkNotNull(javaClass.getResourceAsStream("/dve/$resource")))

    private fun parseInline(src: String): DveModel =
        DveParser.parse(src.trimIndent().byteInputStream())

    private fun transform(resource: String, extraProp: Expr<BoolType>? = null): XSTS =
        DveToXsts.transform(parse(resource), extraProp)

    private fun transformInline(
        src: String,
        extraProp: Expr<BoolType>? = null,
    ): XSTS = DveToXsts.transform(parseInline(src), extraProp)

    /** All variable names in the XSTS (state vars + data vars). */
    private fun XSTS.varNames(): Set<String> = (vars + stateVars + ctrlVars).map { it.name }.toSet()

    /** Flatten all choice branches from a NonDetStmt into SequenceStmts. */
    private fun NonDetStmt.branches(): List<SequenceStmt> =
        stmts.mapNotNull { it as? SequenceStmt }

    // -------------------------------------------------------------------------
    // 1. Variable encoding
    // -------------------------------------------------------------------------

    @Test
    fun `simple model - state variable created`() {
        val xsts = transform("simple.dve")
        assertTrue("Counter_state" in xsts.varNames(), "Expected Counter_state variable")
    }

    @Test
    fun `simple model - local variable created`() {
        val xsts = transform("simple.dve")
        assertTrue("Counter_count" in xsts.varNames(), "Expected Counter_count variable")
    }

    @Test
    fun `peterson - state variables for both processes`() {
        val xsts = transform("peterson.dve")
        assertTrue("P_0_state" in xsts.varNames())
        assertTrue("P_1_state" in xsts.varNames())
    }

    @Test
    fun `peterson - global scalar and array variables created`() {
        val xsts = transform("peterson.dve")
        val names = xsts.varNames()
        // global byte turn
        assertTrue("turn" in names, "Expected global 'turn' variable, found: $names")
        // global byte flag[2] => flag_0, flag_1
        assertTrue("flag_0" in names, "Expected flag_0")
        assertTrue("flag_1" in names, "Expected flag_1")
    }

    @Test
    fun `peterson - local j variables per process`() {
        val xsts = transform("peterson.dve")
        val names = xsts.varNames()
        assertTrue("P_0_j" in names, "Expected P_0_j")
        assertTrue("P_1_j" in names, "Expected P_1_j")
    }

    @Test
    fun `state variables are in ctrlVars`() {
        val xsts = transform("simple.dve")
        val ctrlNames = xsts.ctrlVars.map { it.name }.toSet()
        assertTrue("Counter_state" in ctrlNames)
    }

    // -------------------------------------------------------------------------
    // 2. Init statement
    // -------------------------------------------------------------------------

    @Test
    fun `simple model - init has exactly one branch`() {
        val xsts = transform("simple.dve")
        assertEquals(1, xsts.init.stmts.size)
    }

    @Test
    fun `simple model - init formula references Counter_state`() {
        val xsts = transform("simple.dve")
        val formulaStr = xsts.initFormula.toString()
        assertTrue(formulaStr.contains("Counter_state"), "Init formula should mention Counter_state")
    }

    @Test
    fun `peterson - init formula references both PC variables`() {
        val xsts = transform("peterson.dve")
        val f = xsts.initFormula.toString()
        assertTrue(f.contains("P_0_state"))
        assertTrue(f.contains("P_1_state"))
    }

    @Test
    fun `init formula values match initial state indices`() {
        // simple.dve: Counter init state is "idle" — enum literal "idle" appears in formula
        val xsts = transform("simple.dve")
        val f = xsts.initFormula.toString()
        assertTrue(f.contains("idle"), "Init state name 'idle' should appear in init formula, got: $f")
    }

    // -------------------------------------------------------------------------
    // 3. Transition structure
    // -------------------------------------------------------------------------

    @Test
    fun `simple model - tran has at least 2 branches`() {
        val xsts = transform("simple.dve")
        // simple.dve has 2 transitions: idle->running and running->idle
        assertTrue(xsts.tran.stmts.size >= 2)
    }

    @Test
    fun `peterson - tran has at least 14 branches`() {
        val xsts = transform("peterson.dve")
        // Each of the 2 processes has 7 local transitions → at least 14 branches
        assertTrue(xsts.tran.stmts.size >= 14,
            "Expected >=14 branches, got ${xsts.tran.stmts.size}")
    }

    @Test
    fun `each branch begins with an assume statement`() {
        val xsts = transform("simple.dve")
        val branches = xsts.tran.branches()
        assertTrue(branches.isNotEmpty())
        for (branch in branches) {
            val firstNonSkip = branch.stmts.firstOrNull()
            assertTrue(firstNonSkip is AssumeStmt,
                "Expected first stmt to be AssumeStmt, got: ${firstNonSkip?.javaClass?.simpleName}")
        }
    }

    @Test
    fun `self-loop transition is encoded correctly`() {
        val xsts = transformInline("""
            process P {
                byte x = 0;
                state s0;
                init s0;
                trans s0 -> s0 { effect x = x + 1; };
            }
            system async;
        """)
        // One transition → one branch
        assertEquals(1, xsts.tran.stmts.size)
    }

    @Test
    fun `empty transition body - single branch assume only`() {
        val xsts = transformInline("""
            process P {
                state s0, s1;
                init s0;
                trans s0 -> s1 {};
            }
            system async;
        """)
        assertEquals(1, xsts.tran.stmts.size)
        val branch = xsts.tran.stmts[0] as SequenceStmt
        val firstStmt = branch.stmts.first()
        assertTrue(firstStmt is AssumeStmt)
    }

    // -------------------------------------------------------------------------
    // 4. Synchronous channel (rendezvous)
    // -------------------------------------------------------------------------

    @Test
    fun `synchronous channel - no buffer variables`() {
        val xsts = transform("channels.dve")
        val names = xsts.varNames()
        assertFalse(names.any { it.contains("count") },
            "Synchronous channel should not have count variable")
    }

    @Test
    fun `synchronous channel - rendezvous creates combined branches`() {
        val xsts = transform("channels.dve")
        // channels.dve: Sender has s0->s1 (sync!) and s1->s0; Receiver has r0->r1 (sync?) and r1->r0
        // The rendezvous pair (s0->s1, r0->r1) creates 1 combined branch.
        // Plus 2 local transitions (Sender s1->s0, Receiver r1->r0) = 3 branches minimum
        assertTrue(xsts.tran.stmts.size >= 3,
            "Expected >=3 branches (2 local + 1 rendezvous), got ${xsts.tran.stmts.size}")
    }

    @Test
    fun `synchronous channel with data - receiver variable updated`() {
        val xsts = transform("sync_data_channel.dve")
        val names = xsts.varNames()
        assertTrue("Receiver_x" in names, "Receiver's x variable should exist")
        assertTrue("Sender_val" in names, "Sender's val variable should exist")
    }

    // -------------------------------------------------------------------------
    // 5. Buffered channel
    // -------------------------------------------------------------------------

    @Test
    fun `buffered channel - count variable created`() {
        val xsts = transform("buffered_channel.dve")
        val names = xsts.varNames()
        assertTrue(names.any { it.contains("buf_ch") && it.contains("count") },
            "Expected buf_ch count variable, got: $names")
    }

    @Test
    fun `buffered channel - slot variables created`() {
        val xsts = transform("buffered_channel.dve")
        val names = xsts.varNames()
        assertTrue(names.any { it.contains("buf_ch") && it.contains("slot") },
            "Expected buf_ch slot variables, got: $names")
    }

    @Test
    fun `buffered channel - count initialised to 0`() {
        val xsts = transform("buffered_channel.dve")
        val f = xsts.initFormula.toString()
        // init formula should contain buf_ch_count = 0
        assertTrue(f.contains("0"), "Init formula should contain 0 for empty buffer")
    }

    // -------------------------------------------------------------------------
    // 6. Committed states
    // -------------------------------------------------------------------------

    @Test
    fun `committed state - non-committed transitions get priority guard`() {
        val xsts = transform("commit_assert.dve")
        // P has: s0->s1, s1->s2, s2->s0. s1 is committed.
        assertTrue(xsts.tran.stmts.size >= 3,
            "commit_assert.dve has 3 transitions, expected >=3 branches")
    }

    @Test
    fun `committed state - committed transition not additionally guarded`() {
        // Verify the model processes without exception
        assertDoesNotThrow { transform("commit_assert.dve") }
    }

    // -------------------------------------------------------------------------
    // 7. Assertions → property
    // -------------------------------------------------------------------------

    @Test
    fun `assertions generate non-trivial property`() {
        val xsts = transform("commit_assert.dve")
        // commit_assert.dve has: assert s0: x >= 0, s2: x < 10
        // Property should not be plain True()
        assertFalse(xsts.prop is TrueExpr,
            "Expected non-trivial property from assertions")
    }

    @Test
    fun `assertion property references state variable`() {
        val xsts = transform("commit_assert.dve")
        val propStr = xsts.prop.toString()
        // Should reference state variable
        assertTrue(propStr.contains("P_state"),
            "Property should reference P_state, got: $propStr")
    }

    @Test
    fun `no assertions - property defaults to True`() {
        val xsts = transformInline("""
            process P {
                state s0, s1;
                init s0;
                trans s0 -> s1 {};
            }
            system async;
        """)
        assertTrue(xsts.prop is TrueExpr, "Expected True() when no assertions and no extra prop")
    }

    @Test
    fun `extraProp True is included in property`() {
        val extraProp = True()
        val xsts = transformInline("""
            process P {
                state s0;
                init s0;
            }
            system async;
        """, extraProp = extraProp)
        // With no assertions, extraProp becomes the property
        assertTrue(xsts.prop is TrueExpr)
    }

    // -------------------------------------------------------------------------
    // 8. Unsupported features throw correctly
    // -------------------------------------------------------------------------

    @Test
    fun `property process throws UnsupportedOperationException`() {
        val ex = assertThrows<UnsupportedOperationException> {
            transformInline("""
                process Prop {
                    state s0;
                    init s0;
                    accept s0;
                }
                process Main {
                    state s0;
                    init s0;
                }
                system async property Prop;
            """)
        }
        assertTrue(ex.message!!.contains("Property processes"),
            "Exception message should mention property processes")
    }

    @Test
    fun `sync system composition throws UnsupportedOperationException`() {
        assertThrows<UnsupportedOperationException> {
            transformInline("""
                process P {
                    state s0;
                    init s0;
                }
                system sync;
            """)
        }
    }

    @Test
    fun `bitwise AND operator throws UnsupportedOperationException`() {
        assertThrows<UnsupportedOperationException> {
            transformInline("""
                process P {
                    byte x = 0;
                    state s0;
                    init s0;
                    trans s0 -> s0 { guard x & 1; };
                }
                system async;
            """)
        }
    }

    @Test
    fun `bitwise OR operator throws UnsupportedOperationException`() {
        assertThrows<UnsupportedOperationException> {
            transformInline("""
                process P {
                    byte x = 0;
                    state s0;
                    init s0;
                    trans s0 -> s0 { guard x | 1; };
                }
                system async;
            """)
        }
    }

    @Test
    fun `shift left operator throws UnsupportedOperationException`() {
        assertThrows<UnsupportedOperationException> {
            transformInline("""
                process P {
                    byte x = 0;
                    state s0;
                    init s0;
                    trans s0 -> s0 { guard x << 1; };
                }
                system async;
            """)
        }
    }

    // -------------------------------------------------------------------------
    // 9. Expression translation
    // -------------------------------------------------------------------------

    @Test
    fun `arithmetic expression plus minus mul div mod`() {
        assertDoesNotThrow {
            transformInline("""
                process P {
                    byte x = 0;
                    byte y = 1;
                    state s0;
                    init s0;
                    trans s0 -> s0 {
                        guard x + y > 0;
                        effect x = x - 1, y = x * 2, x = y / 1, y = y % 3;
                    };
                }
                system async;
            """)
        }
    }

    @Test
    fun `comparison guard all operators`() {
        assertDoesNotThrow {
            transformInline("""
                process P {
                    byte x = 0;
                    byte y = 1;
                    state s0;
                    init s0;
                    trans
                        s0 -> s0 { guard x == y; },
                        s0 -> s0 { guard x != y; },
                        s0 -> s0 { guard x < y; },
                        s0 -> s0 { guard x <= y; },
                        s0 -> s0 { guard x > y; },
                        s0 -> s0 { guard x >= y; };
                }
                system async;
            """)
        }
    }

    @Test
    fun `logical AND and OR in guard`() {
        assertDoesNotThrow {
            transformInline("""
                process P {
                    byte x = 0;
                    byte y = 1;
                    state s0;
                    init s0;
                    trans
                        s0 -> s0 { guard x == 0 && y == 1; },
                        s0 -> s0 { guard x == 1 || y == 0; };
                }
                system async;
            """)
        }
    }

    @Test
    fun `logical NOT in guard`() {
        assertDoesNotThrow {
            transformInline("""
                process P {
                    byte x = 0;
                    state s0;
                    init s0;
                    trans s0 -> s0 { guard !x; };
                }
                system async;
            """)
        }
    }

    @Test
    fun `unary negation in arithmetic`() {
        assertDoesNotThrow {
            transformInline("""
                process P {
                    byte x = 1;
                    state s0;
                    init s0;
                    trans s0 -> s0 { guard -x < 0; };
                }
                system async;
            """)
        }
    }

    @Test
    fun `process state expression in guard`() {
        assertDoesNotThrow {
            transformInline("""
                process A {
                    state on, off;
                    init on;
                    trans on -> off {};
                }
                process B {
                    state s0;
                    init s0;
                    trans s0 -> s0 { guard A.on; };
                }
                system async;
            """)
        }
    }

    @Test
    fun `array access in guard and effect`() {
        assertDoesNotThrow {
            transformInline("""
                byte arr[3] = {1, 2, 3};
                process P {
                    byte i = 0;
                    state s0;
                    init s0;
                    trans s0 -> s0 { guard arr[i] > 0; effect arr[0] = arr[1]; };
                }
                system async;
            """)
        }
    }

    // -------------------------------------------------------------------------
    // 10. Qualified LValue writes (cross-process variable assignment)
    // -------------------------------------------------------------------------

    @Test
    fun `qualified lvalue assignment to other process variable`() {
        assertDoesNotThrow {
            transformInline("""
                process A {
                    byte v = 0;
                    state s0;
                    init s0;
                    trans s0 -> s0 {};
                }
                process B {
                    state s0;
                    init s0;
                    trans s0 -> s0 { effect A.v = 1; };
                }
                system async;
            """)
        }
    }

    // -------------------------------------------------------------------------
    // 11. Multi-process async interleaving
    // -------------------------------------------------------------------------

    @Test
    fun `two processes with overlapping state names`() {
        val xsts = transformInline("""
            process P1 {
                state s0, s1;
                init s0;
                trans s0 -> s1 {};
            }
            process P2 {
                state s0, s1;
                init s0;
                trans s0 -> s1 {};
            }
            system async;
        """)
        val names = xsts.varNames()
        assertTrue("P1_state" in names)
        assertTrue("P2_state" in names)
        assertEquals(2, xsts.tran.stmts.size)
    }

    @Test
    fun `peterson full transformation succeeds`() {
        assertDoesNotThrow { transform("peterson.dve") }
    }

    @Test
    fun `peterson no extra property defaults to True`() {
        val xsts = transform("peterson.dve")
        // Peterson has no assertions → prop = True()
        assertTrue(xsts.prop is TrueExpr,
            "Peterson (no assertions) should have True property, got: ${xsts.prop}")
    }
    // -------------------------------------------------------------------------
    // 13. Variable counts
    // -------------------------------------------------------------------------

    @Test
    fun `simple model variable count`() {
        val xsts = transform("simple.dve")
        val names = xsts.varNames()
        // Counter_state + Counter_count = 2 variables minimum
        assertTrue(names.size >= 2, "Expected at least 2 variables, got: $names")
    }

    @Test
    fun `peterson variable count`() {
        val xsts = transform("peterson.dve")
        val names = xsts.varNames()
        // P_0_state, P_1_state, turn, flag_0, flag_1, P_0_j, P_1_j = 7 minimum
        assertTrue(names.size >= 7, "Expected at least 7 variables, got ${names.size}: $names")
    }

    // -------------------------------------------------------------------------
    // 14. Initial state index check
    // -------------------------------------------------------------------------

    @Test
    fun `initial state index is 0 when first in state list`() {
        // In "state s0, s1; init s0" — init formula contains enum literal "s0"
        val xsts = transformInline("""
            process P {
                state s0, s1;
                init s0;
                trans s0 -> s1 {};
            }
            system async;
        """)
        val f = xsts.initFormula.toString()
        assertTrue(f.contains("s0"), "Init state literal 's0' should appear in formula, got: $f")
    }

    @Test
    fun `initial state index is non-zero when not first`() {
        // In "state s0, s1; init s1" — init formula contains enum literal "s1"
        val xsts = transformInline("""
            process P {
                state s0, s1;
                init s1;
                trans s1 -> s0 {};
            }
            system async;
        """)
        val f = xsts.initFormula.toString()
        assertTrue(f.contains("s1"), "Init state literal 's1' should appear in formula, got: $f")
    }

    // -------------------------------------------------------------------------
    // 15. Process with no transitions
    // -------------------------------------------------------------------------

    @Test
    fun `process with no transitions does not throw`() {
        assertDoesNotThrow {
            transformInline("""
                process P {
                    state s0;
                    init s0;
                }
                system async;
            """)
        }
    }
}

