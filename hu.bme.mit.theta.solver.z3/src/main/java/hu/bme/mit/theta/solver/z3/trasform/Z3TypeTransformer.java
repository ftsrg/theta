package hu.bme.mit.theta.solver.z3.trasform;

import com.microsoft.z3.Context;

import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.type.rattype.RatType;

class Z3TypeTransformer {

	@SuppressWarnings("unused")
	private final Z3TransformationManager transformer;
	@SuppressWarnings("unused")
	private final Context context;

	private final com.microsoft.z3.BoolSort boolSort;
	private final com.microsoft.z3.IntSort intSort;
	private final com.microsoft.z3.RealSort realSort;

	Z3TypeTransformer(final Z3TransformationManager transformer, final Context context) {
		this.context = context;
		this.transformer = transformer;

		boolSort = context.mkBoolSort();
		intSort = context.mkIntSort();
		realSort = context.mkRealSort();
	}

	public com.microsoft.z3.Sort toSort(final Type type) {
		if (type instanceof BoolType) {
			return boolSort;
		} else if (type instanceof IntType) {
			return intSort;
		} else if (type instanceof RatType) {
			return realSort;
		} else {
			throw new UnsupportedOperationException();
		}
	}

}
