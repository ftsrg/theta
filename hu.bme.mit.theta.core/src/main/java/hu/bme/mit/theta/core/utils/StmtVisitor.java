/*
 *  Copyright 2017 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.core.stmt.AssertStmt;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.BlockStmt;
import hu.bme.mit.theta.core.stmt.DeclStmt;
import hu.bme.mit.theta.core.stmt.DoStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.stmt.IfElseStmt;
import hu.bme.mit.theta.core.stmt.IfStmt;
import hu.bme.mit.theta.core.stmt.ReturnStmt;
import hu.bme.mit.theta.core.stmt.SkipStmt;
import hu.bme.mit.theta.core.stmt.WhileStmt;
import hu.bme.mit.theta.core.type.Type;

public interface StmtVisitor<P, R> {

	R visit(SkipStmt stmt, P param);

	<DeclType extends Type> R visit(DeclStmt<DeclType> stmt, P param);

	R visit(AssumeStmt stmt, P param);

	R visit(AssertStmt stmt, P param);

	<DeclType extends Type> R visit(AssignStmt<DeclType> stmt, P param);

	<DeclType extends Type> R visit(HavocStmt<DeclType> stmt, P param);

	R visit(BlockStmt stmt, P param);

	<ReturnType extends Type> R visit(ReturnStmt<ReturnType> stmt, P param);

	R visit(IfStmt stmt, P param);

	R visit(IfElseStmt stmt, P param);

	R visit(WhileStmt stmt, P param);

	R visit(DoStmt stmt, P param);

}
