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

package hu.bme.mit.theta.core.serialization

import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.stmt.*
//import hu.bme.mit.theta.core.stmt.generated.stmtSerializer
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.inttype.IntExprs.Eq
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import kotlinx.serialization.encodeToString
import kotlinx.serialization.json.Json
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test

class StmtSerializationTest {

    private val json = Json {
//        serializersModule = stmtSerializer
        classDiscriminator = "type"
    }

    @Test
    fun `test AssignStmt serialization`() {
        val x = Decls.Var("x", Int())
        val original: Stmt = AssignStmt(x, Int(42))
        val serialized = json.encodeToString(original)
        val deserialized = json.decodeFromString<Stmt>(serialized)
        assertEquals(original, deserialized)
        assertEquals("x", (deserialized as AssignStmt<*>).varDecl.name)
    }

    @Test
    fun `test AssumeStmt serialization`() {
        val x = Decls.Var("x", Int())
        val cond = Eq(x.ref, Int(42))
        val original: Stmt = AssumeStmt(cond)
        val serialized = json.encodeToString(original)
        val deserialized = json.decodeFromString<Stmt>(serialized)
        assertEquals(original, deserialized)
        assertEquals("(= x 42)", (deserialized as AssumeStmt).cond.toString())
    }

    @Test
    fun `test HavocStmt serialization`() {
        val x = Decls.Var("x", Int())
        val original: Stmt = HavocStmt(x)
        val serialized = json.encodeToString(original)
        val deserialized = json.decodeFromString<Stmt>(serialized)
        assertEquals(original, deserialized)
        assertEquals("x", (deserialized as HavocStmt<*>).varDecl.name)
    }

    @Test
    fun `test IfStmt serialization`() {
        val x = Decls.Var("x", Int())
        val cond = Eq(x.ref, Int(42))
        val thenStmt: Stmt = AssignStmt(x, Int(1))
        val elseStmt: Stmt = AssignStmt(x, Int(0))
        val original: Stmt = IfStmt(cond, thenStmt, elseStmt)
        val serialized = json.encodeToString(original)
        val deserialized = json.decodeFromString<Stmt>(serialized)
        assertEquals(original, deserialized)
    }

    @Test
    fun `test LoopStmt serialization`() {
        val i = Decls.Var("i", Int())
        val x = Decls.Var("x", Int())
        val stmt: Stmt = AssignStmt(x, Int(1))
        val original: Stmt = LoopStmt(stmt, i, Int(0), Int(42))
        val serialized = json.encodeToString(original)
        val deserialized = json.decodeFromString<Stmt>(serialized)
        assertEquals(original, deserialized)
    }

    @Test
    fun `test MemoryAssignStmt serialization`() {
        val dereference = Dereference(Decls.Var("ptr", Int()).ref, Int(0), Int())
        val original: Stmt = MemoryAssignStmt(dereference, Int(42))
        val serialized = json.encodeToString(original)
        val deserialized = json.decodeFromString<Stmt>(serialized)
        assertEquals(original, deserialized)
    }

    @Test
    fun `test NonDetStmt serialization`() {
        val s1 = AssignStmt(Decls.Var("x", Int()), Int(1))
        val s2 = AssignStmt(Decls.Var("y", Int()), Int(2))
        val s3 = SkipStmt
        val original: Stmt = NonDetStmt(listOf(s1, s2, s3))
        val serialized = json.encodeToString(original)
        val deserialized = json.decodeFromString<Stmt>(serialized)
        assertEquals(original, deserialized)
    }

    @Test
    fun `test OrtStmt serialization`() {
        val s1 = AssignStmt(Decls.Var("x", Int()), Int(1))
        val s2 = AssignStmt(Decls.Var("y", Int()), Int(2))
        val s3 = SkipStmt
        val original: Stmt = OrtStmt(listOf(s1, s2, s3))
        val serialized = json.encodeToString(original)
        val deserialized = json.decodeFromString<Stmt>(serialized)
        assertEquals(original, deserialized)
    }

    @Test
    fun `test SequenceStmt serialization`() {
        val s1 = AssignStmt(Decls.Var("x", Int()), Int(1))
        val s2 = AssignStmt(Decls.Var("y", Int()), Int(2))
        val s3 = SkipStmt
        val original: Stmt = SequenceStmt(listOf(s1, s2, s3))
        val serialized = json.encodeToString(original)
        val deserialized = json.decodeFromString<Stmt>(serialized)
        assertEquals(original, deserialized)
    }

    @Test
    fun `test SkipStmt serialization`() {
        val original: Stmt = SkipStmt
        val serialized = json.encodeToString(original)
        val deserialized = json.decodeFromString<Stmt>(serialized)
        assertEquals(original, deserialized)
    }
}

