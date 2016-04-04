package hu.bme.mit.inf.ttmc.constraint.z3.trasform;

import com.microsoft.z3.Context;
import com.microsoft.z3.Sort;

import hu.bme.mit.inf.ttmc.constraint.type.ArrayType;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.FuncType;
import hu.bme.mit.inf.ttmc.constraint.type.IntType;
import hu.bme.mit.inf.ttmc.constraint.type.RatType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.TypeVisitor;

class Z3TypeVisitor implements TypeVisitor<Void, com.microsoft.z3.Sort> {

	@SuppressWarnings("unused")
	private final Z3Transformator transformator;
	private final Context context;

	private final com.microsoft.z3.BoolSort boolSort;
	private final com.microsoft.z3.IntSort intSort;
	private final com.microsoft.z3.RealSort ratSort;

	Z3TypeVisitor(final Z3Transformator transformator, final Context context) {
		this.context = context;
		this.transformator = transformator;

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
