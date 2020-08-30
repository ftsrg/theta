package hu.bme.mit.theta.solver.smtlib;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.Interpolant;
import hu.bme.mit.theta.solver.ItpMarker;
import hu.bme.mit.theta.solver.ItpPattern;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.SolverStatus;
import hu.bme.mit.theta.solver.Stack;
import hu.bme.mit.theta.solver.impl.ItpPatternImpl;
import hu.bme.mit.theta.solver.impl.StackImpl;

import java.util.Collection;
import java.util.function.Supplier;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

public abstract class SmtLibItpSolver<ItpMarkerType extends SmtLibItpMarker<?>> implements ItpSolver {
    protected final SmtLibSolver solver;
    protected final Stack<ItpMarkerType> markers;
    protected final Supplier<ItpMarkerType> markerCreator;

    protected final SmtLibTransformationManager transformationManager;
    protected final SmtLibTermTransformer termTransformer;

    public SmtLibItpSolver(
        final SmtLibSymbolTable symbolTable, final SmtLibTransformationManager transformationManager,
        final SmtLibTermTransformer termTransformer, final SmtLibSolverBinary solverBinary,
        final Supplier<ItpMarkerType> markerCreator
    ) {
        this.solver = new SmtLibSolver(symbolTable, transformationManager, termTransformer, solverBinary, false);
        this.markers = new StackImpl<>();
        this.markerCreator = markerCreator;

        this.transformationManager = transformationManager;
        this.termTransformer = termTransformer;
    }

    @Override
    public ItpPattern createPattern(ItpMarker marker) {
        checkNotNull(marker);
        checkArgument(marker instanceof SmtLibItpMarker);
        return new ItpPatternImpl(marker);
    }

    @Override
    public ItpMarker createMarker() {
        final ItpMarkerType marker = markerCreator.get();
        markers.add(marker);
        return marker;
    }

    @Override
    public void add(ItpMarker marker, Expr<BoolType> assertion) {
        checkNotNull(marker);
        checkNotNull(assertion);
        checkArgument(markers.toCollection().stream().map(m -> (ItpMarker) m).anyMatch(m -> m == marker));

        final var term = transformationManager.toTerm(assertion);
        add(marker, term);
    }

    protected abstract String add(final ItpMarker marker, final String term);

    @Override
    public abstract Interpolant getInterpolant(ItpPattern pattern);

    // Delegate

    @Override
    public Collection<? extends ItpMarker> getMarkers() {
        return markers.toCollection();
    }

    @Override
    public void add(Expr<BoolType> assertion) {
        solver.add(assertion);
    }

    @Override
    public SolverStatus check() {
        return solver.check();
    }

    @Override
    public void push() {
        markers.push();
        for (final var marker : markers) {
            marker.push();
        }
        solver.push();
    }

    @Override
    public void pop(final int n) {
        markers.pop(n);
        for (final var marker : markers) {
            marker.pop(n);
        }
        solver.pop(n);
    }

    @Override
    public void reset() {
        solver.reset();
    }

    @Override
    public SolverStatus getStatus() {
        return solver.getStatus();
    }

    @Override
    public Valuation getModel() {
        return solver.getModel();
    }

    @Override
    public Collection<Expr<BoolType>> getAssertions() {
        return solver.getAssertions();
    }


}
