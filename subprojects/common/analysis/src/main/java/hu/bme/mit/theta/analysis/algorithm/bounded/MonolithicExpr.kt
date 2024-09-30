/*
 *  Copyright 2024 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.analysis.algorithm.bounded

import hu.bme.mit.theta.analysis.pred.PredPrec
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.anytype.Exprs
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.IffExpr
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.ExprUtils.getVars
import hu.bme.mit.theta.core.utils.indexings.VarIndexing
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory

data class MonolithicExpr @JvmOverloads constructor(
    val initExpr: Expr<BoolType>,
    val transExpr: Expr<BoolType>,
    val propExpr: Expr<BoolType>,
    val transOffsetIndex: VarIndexing = VarIndexingFactory.indexing(1),
    val initOffsetIndex: VarIndexing = VarIndexingFactory.indexing(0),
    val vars: Collection<VarDecl<*>> = getVars(initExpr) union getVars(transExpr) union getVars(propExpr)
)