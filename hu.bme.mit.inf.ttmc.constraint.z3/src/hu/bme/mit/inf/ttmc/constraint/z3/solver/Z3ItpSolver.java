package hu.bme.mit.inf.ttmc.constraint.z3.solver;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import com.microsoft.z3.InterpolationContext;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.solver.Interpolant;
import hu.bme.mit.inf.ttmc.constraint.solver.ItpMarker;
import hu.bme.mit.inf.ttmc.constraint.solver.ItpPattern;
import hu.bme.mit.inf.ttmc.constraint.solver.ItpSolver;
import hu.bme.mit.inf.ttmc.constraint.solver.Model;
import hu.bme.mit.inf.ttmc.constraint.solver.Solver;
import hu.bme.mit.inf.ttmc.constraint.solver.SolverStatus;
import hu.bme.mit.inf.ttmc.constraint.solver.impl.ItpMarkerImpl;
import hu.bme.mit.inf.ttmc.constraint.solver.impl.ItpPatternImpl;
import hu.bme.mit.inf.ttmc.constraint.solver.impl.WrapperExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;

public class Z3ItpSolver implements ItpSolver {

	private final InterpolationContext context;
	private final Z3TermWrapper termWrapper;
	
	private final com.microsoft.z3.Solver z3Solver;
	private final Solver solver;

	private final Collection<ItpMarkerImpl> markers;

	public Z3ItpSolver(final ConstraintManager manager, final InterpolationContext context,
			final Z3TermWrapper termWrapper) {
		this.context = context;
		this.termWrapper = termWrapper;
		
		z3Solver = context.mkSimpleSolver();
		solver = new Z3Solver(manager, context, z3Solver, termWrapper);

		markers = new HashSet<>();
	}
	
	////
	
	private com.microsoft.z3.Expr extractTerm(final Expr<?> expr) {
		final WrapperExpr<?, ?> wExpr = (WrapperExpr<?, ?>) expr;

		final com.microsoft.z3.Expr term = (com.microsoft.z3.Expr) wExpr.getTerm();
		checkNotNull(term);

		return term;
	}

	////

	@Override
	public ItpPattern createPattern(final ItpMarker marker) {
		checkNotNull(marker);
		return new ItpPatternImpl(marker);
	}

	@Override
	public ItpMarker createMarker() {
		final ItpMarkerImpl marker = new ItpMarkerImpl();
		markers.add(marker);
		return marker;
	}

	@Override
	public void add(final ItpMarker marker, final Expr<? extends BoolType> assertion) {
		checkNotNull(marker);
		checkNotNull(assertion);
		checkArgument(markers.contains(marker));

		final ItpMarkerImpl markerImpl = (ItpMarkerImpl) marker;
		markerImpl.add(assertion);
		solver.add(assertion);
	}

	@Override
	public Interpolant getInterpolant(final ItpPattern pattern) {
		checkState(solver.getStatus() == SolverStatus.UNSAT);
		
		final com.microsoft.z3.Expr proof = z3Solver.getProof();
		final com.microsoft.z3.Expr term = patternToTerm(pattern);
		final com.microsoft.z3.Params params = context.mkParams();
		
		final com.microsoft.z3.BoolExpr[] itpArray =  context.GetInterpolant(proof, term, params);
		final List<Expr<BoolType>> itpList = new LinkedList<>();

		for (com.microsoft.z3.BoolExpr itpTerm : itpArray) {
			@SuppressWarnings("unchecked")
			final Expr<BoolType> itpExpr = (Expr<BoolType>) termWrapper.wrap(itpTerm);
			itpList.add(itpExpr);
		}
		
		final Map<ItpMarker, Expr<BoolType>> itpMap = new HashMap<>();
		buildItpMapFormList(pattern, itpList, itpMap);		
		
		return new Z3Interpolant(itpMap);
	}
	
	private com.microsoft.z3.BoolExpr patternToTerm(final ItpPattern pattern) {
		final ItpMarker marker = pattern.getMarker();
		final Collection<? extends Expr<? extends BoolType>> assertions = marker.getAssertions();
				
		final Collection<com.microsoft.z3.BoolExpr> opTerms = new LinkedList<>();	
		for (Expr<? extends BoolType> assertion : assertions) {
			final com.microsoft.z3.BoolExpr subTerm = (com.microsoft.z3.BoolExpr) extractTerm(assertion);
			opTerms.add(subTerm);
		}
		for (ItpPattern child : pattern.getChildren()) {
			final com.microsoft.z3.BoolExpr childTerm = patternToTerm(child);
			opTerms.add(childTerm);
		}

		final com.microsoft.z3.BoolExpr andTerm = context.mkAnd(opTerms.toArray(new com.microsoft.z3.BoolExpr[0]));
		final com.microsoft.z3.BoolExpr term = context.MkInterpolant(andTerm);
		return term;
	}
	
	private void buildItpMapFormList(final ItpPattern pattern, final List<Expr<BoolType>> itpList, final Map<ItpMarker, Expr<BoolType>> itpMap) {
		for (ItpPattern child : pattern.getChildren()) {
			buildItpMapFormList(child, itpList, itpMap);
		}
		final ItpMarker marker = pattern.getMarker();
		final Expr<BoolType> itpExpr = itpList.get(0);
		itpMap.put(marker, itpExpr);
		itpList.remove(0);
	}

	@Override
	public Collection<ItpMarker> getMarkers() {
		return Collections.unmodifiableCollection(markers);
	}

	// delegate

	@Override
	public void add(Expr<? extends BoolType> assertion) {
		checkNotNull(assertion);
		solver.add(assertion);
	}

	@Override
	public void track(Expr<? extends BoolType> assertion) {
		checkNotNull(assertion);
		solver.track(assertion);
	}

	@Override
	public SolverStatus check() {
		return solver.check();
	}

	@Override
	public void push() {
		for (ItpMarkerImpl marker : markers) {
			marker.push();
		}
		solver.push();
	}

	@Override
	public void pop(final int n) {
		for (ItpMarkerImpl marker : markers) {
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
	public Model getModel() {
		return solver.getModel();
	}

	@Override
	public Collection<Expr<? extends BoolType>> getUnsatCore() {
		return solver.getUnsatCore();
	}

	@Override
	public Collection<Expr<? extends BoolType>> getAssertions() {
		return solver.getAssertions();
	}

}
