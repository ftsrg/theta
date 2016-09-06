package hu.bme.mit.inf.theta.solver.z3.trasform;

import com.microsoft.z3.Context;
import com.microsoft.z3.Sort;

import hu.bme.mit.inf.theta.core.type.ArrayType;
import hu.bme.mit.inf.theta.core.type.BoolType;
import hu.bme.mit.inf.theta.core.type.FuncType;
import hu.bme.mit.inf.theta.core.type.IntType;
import hu.bme.mit.inf.theta.core.type.RatType;
import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.core.utils.TypeVisitor;

class Z3TypeTransformer {

	@SuppressWarnings("unused")
	private final Z3TransformationManager transformer;
	private final Context context;

	private final Z3TypeTransformerVisitor visitor;

	Z3TypeTransformer(final Z3TransformationManager transformer, final Context context) {
		this.context = context;
		this.transformer = transformer;
		visitor = new Z3TypeTransformerVisitor();
	}

	public com.microsoft.z3.Sort toSort(final Type type) {
		return type.accept(visitor, null);
	}

	private class Z3TypeTransformerVisitor implements TypeVisitor<Void, com.microsoft.z3.Sort> {
		private final com.microsoft.z3.BoolSort boolSort;
		private final com.microsoft.z3.IntSort intSort;
		private final com.microsoft.z3.RealSort ratSort;

		private Z3TypeTransformerVisitor() {

			boolSort = context.mkBoolSort();
			intSort = context.mkIntSort();
			ratSort = context.mkRealSort();
		}

		@Override
		public com.microsoft.z3.Sort visit(final BoolType type, final Void param) {
			return boolSort;
		}

		@Override
		public com.microsoft.z3.Sort visit(final IntType type, final Void param) {
			return intSort;
		}

		@Override
		public com.microsoft.z3.Sort visit(final RatType type, final Void param) {
			return ratSort;
		}

		@Override
		public <ParamType extends Type, ResultType extends Type> com.microsoft.z3.Sort visit(
				final FuncType<ParamType, ResultType> type, final Void param) {
			// TODO Auto-generated method stub
			throw new UnsupportedOperationException("TODO: auto-generated method stub");
		}

		@Override
		public <IndexType extends Type, ElemType extends Type> com.microsoft.z3.Sort visit(
				final ArrayType<IndexType, ElemType> type, final Void param) {
			final Sort indexSort = type.getIndexType().accept(this, param);
			final Sort elemSort = type.getElemType().accept(this, param);
			return context.mkArraySort(indexSort, elemSort);
		}

	}

}
