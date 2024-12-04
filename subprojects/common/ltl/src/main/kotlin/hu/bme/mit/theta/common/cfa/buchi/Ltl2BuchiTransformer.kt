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
package hu.bme.mit.theta.common.cfa.buchi

import hu.bme.mit.theta.cfa.CFA
import hu.bme.mit.theta.core.decl.VarDecl

fun interface Ltl2BuchiTransformer {

  fun transform(ltl: String, variableMapping: Map<String, VarDecl<*>>): CFA

  fun transform(ltl: String, variables: Collection<VarDecl<*>>): CFA =
    transform(ltl, variables.associateBy { it.name })
}
