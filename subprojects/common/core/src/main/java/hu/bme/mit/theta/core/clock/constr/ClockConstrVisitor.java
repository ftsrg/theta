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
package hu.bme.mit.theta.core.clock.constr;

public interface ClockConstrVisitor<P, R> {

    R visit(final TrueConstr constr, final P param);

    R visit(final FalseConstr constr, final P param);

    R visit(final UnitLtConstr constr, final P param);

    R visit(final UnitLeqConstr constr, final P param);

    R visit(final UnitGtConstr constr, final P param);

    R visit(final UnitGeqConstr constr, final P param);

    R visit(final UnitEqConstr constr, final P param);

    R visit(final DiffLtConstr constr, final P param);

    R visit(final DiffLeqConstr constr, final P param);

    R visit(final DiffGtConstr constr, final P param);

    R visit(final DiffGeqConstr constr, final P param);

    R visit(final DiffEqConstr constr, final P param);

    R visit(final AndConstr constr, final P param);
}
