package hu.bme.mit.inf.ttmc.constraint.z3.type;

import com.microsoft.z3.Context;
import com.microsoft.z3.IntSort;

import hu.bme.mit.inf.ttmc.constraint.type.impl.IntTypeImpl;

public class Z3IntType extends IntTypeImpl implements Z3Type {

	private final Context context;
	
	private volatile IntSort sort;
	
	public Z3IntType(final Context context) {
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
