package hu.bme.mit.inf.ttmc.constraint.z3.type;

import com.microsoft.z3.BoolSort;
import com.microsoft.z3.Context;

import hu.bme.mit.inf.ttmc.constraint.type.defaults.AbstractBoolType;

public class Z3BoolType extends AbstractBoolType implements Z3Type {

	private final Context context;
	
	private volatile BoolSort sort;
	
	public Z3BoolType(final Context context) {
		this.context = context;
	}

	@Override
	public BoolSort getSort() {
		if (sort == null) {
			sort = context.mkBoolSort();
		}
		
		return sort;
	}

}
