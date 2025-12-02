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

package hu.bme.mit.theta.solver.meta;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.Interpolant;
import hu.bme.mit.theta.solver.ItpMarker;
import hu.bme.mit.theta.solver.ItpSolver;

import static com.google.common.base.Preconditions.checkArgument;

public class MetaInterpolant implements Interpolant {
    private final ItpSolver solver;
    private final Interpolant interpolant;
    public MetaInterpolant( final ItpSolver solver, final Interpolant interpolant ) {
        this.solver = solver;
        this.interpolant = interpolant;
    }
    @Override
    public Expr<BoolType> eval(ItpMarker marker) {
        checkArgument(marker instanceof MetaItpMarker);
        return interpolant.eval(((MetaItpMarker) marker).getMarker(solver));
    }
}
