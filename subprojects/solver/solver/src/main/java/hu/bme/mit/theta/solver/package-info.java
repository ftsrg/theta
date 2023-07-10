/*
 *  Copyright 2023 Budapest University of Technology and Economics
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
/**
 * This package contains the generic interfaces for SMT solvers. Use a concrete implementation of
 * {@link hu.bme.mit.theta.solver.SolverFactory} to create a {@link hu.bme.mit.theta.solver.Solver}
 * or an {@link hu.bme.mit.theta.solver.ItpSolver} for interpolation. See
 * {@link hu.bme.mit.theta.solver.Solver} for more information about using solvers.
 */

package hu.bme.mit.theta.solver;