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

package hu.bme.mit.theta.frontend.dve

import hu.bme.mit.theta.frontend.dve.model.*
import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.api.Test

class DveParserTest {

  private fun parse(resource: String) =
    DveParser.parse(checkNotNull(javaClass.getResourceAsStream("/dve/$resource")))

  // -------------------------------------------------------------------------
  // Simple model
  // -------------------------------------------------------------------------

  @Test
  fun `simple model parses correctly`() {
    val model = parse("simple.dve")

    assertEquals(1, model.processes.size)
    val proc = model.processes[0]
    assertEquals("Counter", proc.name)
    assertEquals(listOf("idle", "running"), proc.states)
    assertEquals("idle", proc.initialState)
    assertEquals(2, proc.transitions.size)

    // First transition: idle -> running { guard count < 5; effect count = count + 1; }
    val t0 = proc.transitions[0]
    assertEquals("idle", t0.sourceState)
    assertEquals("running", t0.targetState)
    assertNotNull(t0.guard)
    assertEquals(1, t0.effects.size)

    // Second transition: running -> idle {}
    val t1 = proc.transitions[1]
    assertEquals("running", t1.sourceState)
    assertEquals("idle", t1.targetState)
    assertNull(t1.guard)
    assertTrue(t1.effects.isEmpty())

    assertEquals(DveSystemType.ASYNC, model.system.type)
    assertNull(model.system.propertyProcessName)
  }

  @Test
  fun `simple model local variable parsed`() {
    val model = parse("simple.dve")
    val proc = model.processes[0]
    assertEquals(1, proc.variables.size)
    val v = proc.variables[0] as DveVarOrArrayDecl.Scalar
    assertEquals("count", v.decl.name)
    assertEquals(DveVariableType.BYTE, v.decl.type)
    assertEquals(DveExpression.LiteralExpr(0), v.decl.initialValue)
  }

  // -------------------------------------------------------------------------
  // Peterson's mutex
  // -------------------------------------------------------------------------

  @Test
  fun `peterson model parses two processes`() {
    val model = parse("peterson.dve")
    assertEquals(2, model.processes.size)
    assertEquals("P_0", model.processes[0].name)
    assertEquals("P_1", model.processes[1].name)
  }

  @Test
  fun `peterson global variables`() {
    val model = parse("peterson.dve")

    // byte turn = 0
    val turn = (model.globalVariables[0] as DveVarOrArrayDecl.Scalar).decl
    assertEquals("turn", turn.name)
    assertEquals(DveVariableType.BYTE, turn.type)
    assertEquals(DveExpression.LiteralExpr(0), turn.initialValue)

    // byte flag[2] = {0, 0}
    val flag = (model.globalVariables[1] as DveVarOrArrayDecl.Array).decl
    assertEquals("flag", flag.name)
    assertEquals(2, flag.size)
    assertEquals(2, flag.initialValues?.size)
  }

  @Test
  fun `peterson transitions count`() {
    val model = parse("peterson.dve")
    assertEquals(7, model.processes[0].transitions.size)
    assertEquals(7, model.processes[1].transitions.size)
  }

  @Test
  fun `peterson guard expression structure`() {
    val model = parse("peterson.dve")
    // q2 -> q3 { guard j < 2; }  — second transition in P_0
    val guard = model.processes[0].transitions[1].guard
    assertNotNull(guard)
    guard as DveExpression.BinaryExpr
    assertEquals(DveBinaryOp.LT, guard.op)
    assertEquals(DveExpression.VarRefExpr(null, "j"), guard.left)
    assertEquals(DveExpression.LiteralExpr(2), guard.right)
  }

  // -------------------------------------------------------------------------
  // Channels
  // -------------------------------------------------------------------------

  @Test
  fun `synchronous channel parsed`() {
    val model = parse("channels.dve")
    assertEquals(1, model.channels.size)
    val ch = model.channels[0]
    assertEquals("sync_ch", ch.name)
    assertEquals(0, ch.bufferSize)
    assertTrue(ch.typedFields.isEmpty())
  }

  @Test
  fun `send sync action parsed`() {
    val model = parse("channels.dve")
    val sender = model.processes[0]
    val t = sender.transitions[0]
    assertNotNull(t.sync)
    val send = t.sync as DveSyncAction.Send
    assertEquals("sync_ch", send.channelName)
    assertTrue(send.values.isEmpty())
  }

  @Test
  fun `receive sync action parsed`() {
    val model = parse("channels.dve")
    val receiver = model.processes[1]
    val t = receiver.transitions[0]
    assertNotNull(t.sync)
    val recv = t.sync as DveSyncAction.Receive
    assertEquals("sync_ch", recv.channelName)
    assertTrue(recv.variables.isEmpty())
  }

  // -------------------------------------------------------------------------
  // Committed states and assertions
  // -------------------------------------------------------------------------

  @Test
  fun `committed states parsed`() {
    val model = parse("commit_assert.dve")
    val proc = model.processes[0]
    assertEquals(listOf("s1"), proc.committedStates)
  }

  @Test
  fun `assertions parsed`() {
    val model = parse("commit_assert.dve")
    val proc = model.processes[0]
    assertEquals(2, proc.assertions.size)
    assertEquals("s0", proc.assertions[0].stateName)
    assertEquals("s2", proc.assertions[1].stateName)
  }

  // -------------------------------------------------------------------------
  // Qualified reference resolution
  // -------------------------------------------------------------------------

  @Test
  fun `process state reference resolved correctly`() {
    val model = parse("peterson.dve")
    // P_0 has state "NCS"; P_0.NCS should become ProcessStateExpr
    // Synthesize a small model with a property to test resolution
    val src =
      """
            process A {
                state on, off;
                init on;
                trans on -> off {};
            }
            process B {
                state x;
                init x;
                // Guard references A's state
                trans x -> x { guard A.on == A.off; };
            }
            system async;
        """
        .trimIndent()
    val m = DveParser.parse(src.byteInputStream())
    val guard = m.processes[1].transitions[0].guard as DveExpression.BinaryExpr
    assertTrue(guard.left is DveExpression.ProcessStateExpr)
    assertTrue(guard.right is DveExpression.ProcessStateExpr)
  }

  @Test
  fun `qualified variable reference not misidentified as state`() {
    val src =
      """
            process A {
                byte v = 0;
                state s0;
                init s0;
                trans s0 -> s0 {};
            }
            process B {
                state s0;
                init s0;
                trans s0 -> s0 { guard A.v == 0; };
            }
            system async;
        """
        .trimIndent()
    val m = DveParser.parse(src.byteInputStream())
    val guard = m.processes[1].transitions[0].guard as DveExpression.BinaryExpr
    // A.v — 'v' is not a state of A, so must resolve to VarRefExpr
    val ref = guard.left as DveExpression.VarRefExpr
    assertEquals("A", ref.processName)
    assertEquals("v", ref.varName)
  }

  // -------------------------------------------------------------------------
  // Edge cases
  // -------------------------------------------------------------------------

  @Test
  fun `empty transition body parses`() {
    val src =
      """
            process P {
                state s0, s1;
                init s0;
                trans s0 -> s1 {};
            }
            system async;
        """
        .trimIndent()
    val m = DveParser.parse(src.byteInputStream())
    val t = m.processes[0].transitions[0]
    assertNull(t.guard)
    assertNull(t.sync)
    assertTrue(t.effects.isEmpty())
  }

  @Test
  fun `self-loop transition parses`() {
    val src =
      """
            process P {
                byte x = 0;
                state s0;
                init s0;
                trans s0 -> s0 { effect x = x + 1; };
            }
            system async;
        """
        .trimIndent()
    val m = DveParser.parse(src.byteInputStream())
    val t = m.processes[0].transitions[0]
    assertEquals("s0", t.sourceState)
    assertEquals("s0", t.targetState)
  }

  @Test
  fun `system async property parsed`() {
    val src =
      """
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
        """
        .trimIndent()
    val m = DveParser.parse(src.byteInputStream())
    assertEquals("Prop", m.system.propertyProcessName)
  }

  @Test
  fun `unary negation expression`() {
    val src =
      """
            process P {
                byte x = 0;
                state s0;
                init s0;
                trans s0 -> s0 { guard -x == 0; };
            }
            system async;
        """
        .trimIndent()
    val m = DveParser.parse(src.byteInputStream())
    val guard = m.processes[0].transitions[0].guard as DveExpression.BinaryExpr
    val lhs = guard.left as DveExpression.UnaryExpr
    assertEquals(DveUnaryOp.NEG, lhs.op)
  }

  @Test
  fun `mixed scalar and array declaration in process`() {
    val src =
      """
            process P {
                byte list[3], len, i;
                state s0;
                init s0;
                trans s0 -> s0 { guard len == 0; };
            }
            system async;
        """
        .trimIndent()
    val m = DveParser.parse(src.byteInputStream())
    val proc = m.processes[0]
    assertEquals(3, proc.variables.size)
    // list[3] is an array
    val arr = proc.variables[0] as DveVarOrArrayDecl.Array
    assertEquals("list", arr.decl.name)
    assertEquals(3, arr.decl.size)
    // len and i are scalars
    val len = proc.variables[1] as DveVarOrArrayDecl.Scalar
    assertEquals("len", len.decl.name)
    val i = proc.variables[2] as DveVarOrArrayDecl.Scalar
    assertEquals("i", i.decl.name)
  }

  @Test
  fun `process-local pure array declaration`() {
    val src =
      """
            process P {
                byte recbuf[3], nakd[3];
                state s0;
                init s0;
            }
            system async;
        """
        .trimIndent()
    val m = DveParser.parse(src.byteInputStream())
    val proc = m.processes[0]
    assertEquals(2, proc.variables.size)
    val a1 = proc.variables[0] as DveVarOrArrayDecl.Array
    assertEquals("recbuf", a1.decl.name)
    assertEquals(3, a1.decl.size)
    val a2 = proc.variables[1] as DveVarOrArrayDecl.Array
    assertEquals("nakd", a2.decl.name)
    assertEquals(3, a2.decl.size)
  }

  @Test
  fun `array access in expression`() {
    val src =
      """
            byte arr[3] = {1, 2, 3};
            process P {
                state s0;
                init s0;
                trans s0 -> s0 { guard arr[0] == 1; };
            }
            system async;
        """
        .trimIndent()
    val m = DveParser.parse(src.byteInputStream())
    val guard = m.processes[0].transitions[0].guard as DveExpression.BinaryExpr
    val access = guard.left as DveExpression.ArrayAccessExpr
    assertEquals("arr", access.varName)
    assertNull(access.processName)
    assertEquals(DveExpression.LiteralExpr(0), access.index)
  }
}
