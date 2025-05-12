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
package hu.bme.mit.theta.solver.logger;

import hu.bme.mit.theta.core.Relation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.*;
import java.util.Collection;
import java.util.List;
import java.util.Set;

/** Records solver calls. Use whenToSave to direct when to persist the calls to file. */
public final class SolverLoggerWrapper implements Solver, UCSolver, ItpSolver, HornSolver {
    private final SolverBase solverBase;
    private final TermLogger termLogger;
    private final Set<SaveStrategy> whenToSave;

    public SolverLoggerWrapper(
            SolverBase solverBase, TermLogger termLogger, Set<SaveStrategy> whenToSave) {
        this.solverBase = solverBase;
        this.termLogger = termLogger;
        this.whenToSave = whenToSave;
    }

    public enum SaveStrategy {
        ON_ADD,
        ON_POP,
        ON_CHECK, /* check, get unsat core, interpolate, etc */
        ON_RESET,
    }

    private void save(SaveStrategy saveStrategy) {
        if (saveStrategy != null && whenToSave.contains(saveStrategy)) {
            termLogger.endCurrentFile();
        }
    }

    // Solver
    @Override
    public void add(Expr<BoolType> assertion) {
        if (solverBase instanceof Solver solver) {
            termLogger.getSolver().add(assertion);
            save(SaveStrategy.ON_ADD);
            solver.add(assertion);
        }
    }

    @Override
    public void add(Iterable<? extends Expr<BoolType>> assertions) {
        if (solverBase instanceof Solver solver) {
            termLogger.getSolver().add(assertions);
            save(SaveStrategy.ON_ADD);
            solver.add(assertions);
        }
    }

    // UCSolver

    @Override
    public void track(Expr<BoolType> assertion) {
        if (solverBase instanceof UCSolver ucSolver) {
            termLogger.getUCSolver().track(assertion);
            save(SaveStrategy.ON_ADD);
            ucSolver.track(assertion);
        }
    }

    @Override
    public void track(Iterable<? extends Expr<BoolType>> assertions) {
        if (solverBase instanceof UCSolver ucSolver) {
            termLogger.getUCSolver().track(assertions);
            save(SaveStrategy.ON_ADD);
            ucSolver.track(assertions);
        }
    }

    @Override
    public Collection<Expr<BoolType>> getUnsatCore() {
        if (solverBase instanceof UCSolver ucSolver) {
            try {
                termLogger.getUCSolver().getUnsatCore();
            } catch (Throwable ignored) {

            }
            save(SaveStrategy.ON_CHECK);
            return ucSolver.getUnsatCore();
        }
        return null;
    }

    // ItpSolver

    @Override
    public ItpPattern createBinPattern(ItpMarker markerA, ItpMarker markerB) {
        if (solverBase instanceof ItpSolver itpSolver) {
            try {
                termLogger.getItpSolver().createBinPattern(markerA, markerB);
            } catch (Throwable ignored) {

            }
            return itpSolver.createBinPattern(markerA, markerB);
        }
        return null;
    }

    @Override
    public ItpPattern createSeqPattern(List<? extends ItpMarker> markers) {
        if (solverBase instanceof ItpSolver itpSolver) {
            try {
                termLogger.getItpSolver().createSeqPattern(markers);
            } catch (Throwable ignored) {

            }
            return itpSolver.createSeqPattern(markers);
        }
        return null;
    }

    @Override
    public ItpPattern createTreePattern(ItpMarkerTree<? extends ItpMarker> root) {
        if (solverBase instanceof ItpSolver itpSolver) {
            try {
                termLogger.getItpSolver().createTreePattern(root);
            } catch (Throwable ignored) {

            }
            return itpSolver.createTreePattern(root);
        }
        return null;
    }

    @Override
    public ItpMarker createMarker() {
        if (solverBase instanceof ItpSolver itpSolver) {
            try {
                termLogger.getItpSolver().createMarker();
            } catch (Throwable ignored) {

            }
            return itpSolver.createMarker();
        }
        return null;
    }

    @Override
    public void add(ItpMarker marker, Expr<BoolType> assertion) {
        if (solverBase instanceof ItpSolver itpSolver) {
            termLogger.getItpSolver().add(marker, assertion);
            save(SaveStrategy.ON_ADD);
            itpSolver.add(marker, assertion);
        }
    }

    @Override
    public void add(ItpMarker marker, Iterable<? extends Expr<BoolType>> assertions) {
        if (solverBase instanceof ItpSolver itpSolver) {
            termLogger.getItpSolver().add(marker, assertions);
            save(SaveStrategy.ON_ADD);
            itpSolver.add(marker, assertions);
        }
    }

    @Override
    public Interpolant getInterpolant(ItpPattern pattern) {
        if (solverBase instanceof ItpSolver itpSolver) {
            try {
                termLogger.getItpSolver().getInterpolant(pattern);
            } catch (Throwable ignored) {

            }
            save(SaveStrategy.ON_CHECK);
            return itpSolver.getInterpolant(pattern);
        }
        return null;
    }

    @Override
    public Collection<? extends ItpMarker> getMarkers() {
        if (solverBase instanceof ItpSolver itpSolver) {
            try {
                termLogger.getItpSolver().getMarkers();
            } catch (Throwable ignored) {

            }
            return itpSolver.getMarkers();
        }
        return null;
    }

    // HornSolver

    @Override
    public void add(Relation relation) {
        if (solverBase instanceof HornSolver hornSolver) {
            termLogger.getHornSolver().add(relation);
            save(SaveStrategy.ON_ADD);
            hornSolver.add(relation);
        }
    }

    @Override
    public void add(Collection<? extends Relation> relations) {
        if (solverBase instanceof HornSolver hornSolver) {
            termLogger.getHornSolver().add(relations);
            save(SaveStrategy.ON_ADD);
            hornSolver.add(relations);
        }
    }

    @Override
    public ProofNode getProof() {
        if (solverBase instanceof HornSolver hornSolver) {
            try {
                termLogger.getHornSolver().getProof();
            } catch (Throwable ignored) {

            }
            save(SaveStrategy.ON_CHECK);
            return hornSolver.getProof();
        } else if (solverBase instanceof Solver solver) {
            try {
                termLogger.getSolver().getProof();
            } catch (Throwable ignored) {

            }
            save(SaveStrategy.ON_CHECK);
            return solver.getProof();
        }
        return null;
    }

    // SolverBase

    @Override
    public SolverStatus check() {
        try {
            if (solverBase instanceof HornSolver) {
                termLogger.getHornSolver().check();
            } else if (solverBase instanceof Solver) {
                termLogger.getSolver().check();
            } else if (solverBase instanceof UCSolver) {
                termLogger.getUCSolver().check();
            } else if (solverBase instanceof ItpSolver) {
                termLogger.getItpSolver().check();
            }
        } catch (Throwable ignored) {

        }
        save(SaveStrategy.ON_CHECK);
        return solverBase.check();
    }

    @Override
    public void push() {
        try {
            if (solverBase instanceof HornSolver) {
                termLogger.getHornSolver().push();
            } else if (solverBase instanceof Solver) {
                termLogger.getSolver().push();
            } else if (solverBase instanceof UCSolver) {
                termLogger.getUCSolver().push();
            } else if (solverBase instanceof ItpSolver) {
                termLogger.getItpSolver().push();
            }
        } catch (Throwable ignored) {

        }
        solverBase.push();
    }

    @Override
    public void pop(int n) {
        try {
            if (solverBase instanceof HornSolver) {
                termLogger.getHornSolver().pop(n);
            } else if (solverBase instanceof Solver) {
                termLogger.getSolver().pop(n);
            } else if (solverBase instanceof UCSolver) {
                termLogger.getUCSolver().pop(n);
            } else if (solverBase instanceof ItpSolver) {
                termLogger.getItpSolver().pop(n);
            }
        } catch (Throwable ignored) {

        }
        save(SaveStrategy.ON_POP);
        solverBase.pop(n);
    }

    @Override
    public void reset() {
        try {
            if (solverBase instanceof HornSolver) {
                termLogger.getHornSolver().reset();
            } else if (solverBase instanceof Solver) {
                termLogger.getSolver().reset();
            } else if (solverBase instanceof UCSolver) {
                termLogger.getUCSolver().reset();
            } else if (solverBase instanceof ItpSolver) {
                termLogger.getItpSolver().reset();
            }
        } catch (Throwable ignored) {

        }
        save(SaveStrategy.ON_RESET);
        solverBase.reset();
    }

    @Override
    public SolverStatus getStatus() {
        return solverBase.getStatus();
    }

    @Override
    public Valuation getModel() {
        return solverBase.getModel();
    }

    @Override
    public Collection<Expr<BoolType>> getAssertions() {
        return solverBase.getAssertions();
    }

    @Override
    public void close() throws Exception {}
}
