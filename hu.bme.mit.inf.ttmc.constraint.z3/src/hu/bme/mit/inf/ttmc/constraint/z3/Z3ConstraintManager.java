package hu.bme.mit.inf.ttmc.constraint.z3;

import com.microsoft.z3.InterpolationContext;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.factory.DeclFactory;
import hu.bme.mit.inf.ttmc.constraint.factory.ExprFactory;
import hu.bme.mit.inf.ttmc.constraint.factory.SolverFactory;
import hu.bme.mit.inf.ttmc.constraint.factory.TypeFactory;
import hu.bme.mit.inf.ttmc.constraint.z3.factory.Z3DeclFactory;
import hu.bme.mit.inf.ttmc.constraint.z3.factory.Z3ExprFactory;
import hu.bme.mit.inf.ttmc.constraint.z3.factory.Z3SolverFactory;
import hu.bme.mit.inf.ttmc.constraint.z3.factory.Z3TypeFactory;
import hu.bme.mit.inf.ttmc.constraint.z3.solver.Z3TermWrapper;
import hu.bme.mit.inf.ttmc.constraint.z3.solver.Z3TermWrapperImpl;

public final class Z3ConstraintManager implements ConstraintManager {

	final Z3DeclFactory declFactory;
	final Z3TypeFactory typeFactory;
	final Z3ExprFactory exprFactory;
	final Z3SolverFactory solverFactory;

	public Z3ConstraintManager() {
		// final Map<String, String> config = new HashMap<String, String>();
		// // Turn model generation on
		// config.put("model", "true");
		// // Turn proof generation on
		// config.put("proof", "true");
		//
		final InterpolationContext context = new InterpolationContext();
		declFactory = new Z3DeclFactory(this, context);
		typeFactory = new Z3TypeFactory(this, context);
		exprFactory = new Z3ExprFactory(this, context);

		final Z3TermWrapper termWrapper = new Z3TermWrapperImpl(this, context, declFactory);
		solverFactory = new Z3SolverFactory(this, context, termWrapper);
	}

	static {
		loadLibraries();
	}

	private static void loadLibraries() {
		System.loadLibrary("msvcr110");
		System.loadLibrary("msvcp110");
		System.loadLibrary("vcomp110");
		System.loadLibrary("libz3");
		System.loadLibrary("libz3java");
	}

	@Override
	public DeclFactory getDeclFactory() {
		return declFactory;
	}

	@Override
	public TypeFactory getTypeFactory() {
		return typeFactory;
	}

	@Override
	public ExprFactory getExprFactory() {
		return exprFactory;
	}

	@Override
	public SolverFactory getSolverFactory() {
		return solverFactory;
	}

}
