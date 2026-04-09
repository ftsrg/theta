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
package hu.bme.mit.theta.solver.impl;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.*;

import java.util.Collection;
import java.util.List;

public final class NullSolver implements Solver, ItpSolver, UCSolver {

    private final RuntimeException exception;

    private NullSolver(final RuntimeException exception) {
        this.exception = exception;
    }

    private static class LazyHolder {
        static final NullSolver INSTANCE =
            new NullSolver(new UnsupportedOperationException());
    }

    public static NullSolver getInstance() {
        return LazyHolder.INSTANCE;
    }

    public static NullSolver withException(final Throwable t) {
        final RuntimeException ex =
            (t instanceof RuntimeException)
                ? (RuntimeException) t
                : new RuntimeException(t);
        return new NullSolver(ex);
    }

    private RuntimeException ex() {
        return exception;
    }

    private <T> T fail() {
        throw ex();
    }

    @Override
    public void add(final Expr<BoolType> assertion) {
        throw ex();
    }

    @Override
    public SolverStatus check() {
        return fail();
    }

    @Override
    public void push() {
        throw ex();
    }

    @Override
    public void pop(final int n) {
        throw ex();
    }

    @Override
    public void reset() {
        throw ex();
    }

    @Override
    public SolverStatus getStatus() {
        return fail();
    }

    @Override
    public Valuation getModel() {
        return fail();
    }

    @Override
    public Collection<Expr<BoolType>> getAssertions() {
        return fail();
    }

    @Override
    public void close() throws Exception {
        throw ex();
    }

    @Override
    public ItpPattern createTreePattern(ItpMarkerTree<? extends ItpMarker> root) {
        return fail();
    }

    @Override
    public ItpMarker createMarker() {
        return fail();
    }

    @Override
    public void add(ItpMarker marker, Expr<BoolType> assertion) {
        throw ex();
    }

    @Override
    public Interpolant getInterpolant(ItpPattern pattern) {
        return fail();
    }

    @Override
    public Collection<? extends ItpMarker> getMarkers() {
        return fail();
    }

    @Override
    public void track(Expr<BoolType> assertion) {
        throw ex();
    }

    @Override
    public Collection<Expr<BoolType>> getUnsatCore() {
        return fail();
    }
}