package hu.bme.mit.inf.ttmc.constraint.z3.type;

import com.microsoft.z3.ArraySort;
import com.microsoft.z3.Context;
import com.microsoft.z3.Sort;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.type.defaults.AbstractArrayType;

public class Z3ArrayType<IndexType extends Type, ElemType extends Type> extends AbstractArrayType<IndexType, ElemType>
		implements Z3Type {

	private final Context context;

	private volatile ArraySort sort;

	public Z3ArrayType(final ConstraintManager manager, final IndexType indexType, final ElemType elemType,
			final Context context) {
		super(manager, indexType, elemType);
		this.context = context;
	}

	@Override
	public ArraySort getSort() {
		if (sort == null) {
			final Sort indexSort = ((Z3Type) getIndexType()).getSort();
			final Sort elemSort = ((Z3Type) getElemType()).getSort();
			sort = context.mkArraySort(indexSort, elemSort);
		}

		return sort;
	}
}
