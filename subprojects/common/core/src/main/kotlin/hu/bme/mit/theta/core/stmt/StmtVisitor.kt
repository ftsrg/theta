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
package hu.bme.mit.theta.core.stmt

import hu.bme.mit.theta.core.type.Type

/**
 * Visitor interface for the statement hierarchy.
 *
 * @param <P> The type of the parameter
 * @param <R> The return type of the visit operations
 */
interface StmtVisitor<in P, out R> {
  fun visit(stmt: SkipStmt, param: P): R

  fun visit(stmt: AssumeStmt, param: P): R

  fun <DeclType : Type> visit(stmt: AssignStmt<DeclType>, param: P): R

  fun <PtrType : Type, OffsetType : Type, DeclType : Type> visit(
    stmt: MemoryAssignStmt<PtrType, OffsetType, DeclType>,
    param: P,
  ): R

  fun <DeclType : Type> visit(stmt: HavocStmt<DeclType>, param: P): R

  fun visit(stmt: SequenceStmt, param: P): R

  fun visit(stmt: NonDetStmt, param: P): R

  fun visit(stmt: OrtStmt, param: P): R

  fun visit(stmt: LoopStmt, param: P): R

  fun visit(stmt: IfStmt, param: P): R
}
