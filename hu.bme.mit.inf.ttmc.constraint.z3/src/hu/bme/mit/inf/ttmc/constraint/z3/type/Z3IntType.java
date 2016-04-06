package hu.bme.mit.inf.ttmc.constraint.z3.type;

import com.microsoft.z3.Context;
import com.microsoft.z3.IntSort;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.type.defaults.AbstractIntType;

public class Z3IntType extends AbstractIntType implements Z3Type {

	private final Context context;

	private volatile IntSort sort;

	public Z3IntType(final ConstraintManager manager, final Context context) {
		super(manager);
		this.context = context;
	}

	@Override
	public IntSort getSort() {
		if (sort == null) {
			sort = context.mkIntSort();
		}

		return sort;
	}

}
