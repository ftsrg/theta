/*
 *  Copyright 2022 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.xcfa.model

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import java.util.Optional

sealed class XcfaLabel

data class InvokeLabel(
        val name: String,
        val params: List<Expr<*>>
) : XcfaLabel()

data class StartLabel(
        val name: String,
        val params: List<Expr<*>>,
        val pidVar: VarDecl<*>
) : XcfaLabel()

data class JoinLabel(
        val pid: Expr<*>
) : XcfaLabel()

data class StmtLabel(
        val stmt: hu.bme.mit.theta.core.stmt.Stmt
) : XcfaLabel()

data class ReadLabel(
        val local: VarDecl<*>,
        val global: VarDecl<*>,
        val labels: Set<String>
) : XcfaLabel()

data class WriteLabel(
        val local: VarDecl<*>,
        val global: VarDecl<*>,
        val labels: Set<String>
) : XcfaLabel()

data class FenceLabel(
        val labels: Set<String>
) : XcfaLabel()

data class SequenceLabel(
        val labels: List<XcfaLabel>
) : XcfaLabel()

data class NondetLabel(
        val labels: Set<XcfaLabel>
) : XcfaLabel()
