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
package hu.bme.mit.theta.graphsolver.solvers

import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.solver.SolverStatus

interface GraphSolver<T> {

  fun add(t: T)

  fun getAll(): Collection<T>

  fun check(): SolverStatus

  fun getModel(): Valuation
}
