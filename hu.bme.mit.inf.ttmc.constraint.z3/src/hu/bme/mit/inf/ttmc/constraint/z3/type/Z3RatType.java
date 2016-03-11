package hu.bme.mit.inf.ttmc.constraint.z3.type;

import com.microsoft.z3.Context;
import com.microsoft.z3.RealSort;

import hu.bme.mit.inf.ttmc.constraint.type.defaults.AbstractRatType;

public class Z3RatType extends AbstractRatType implements Z3Type {

	private final Context context;
	
	private volatile RealSort sort;
	
	public Z3RatType(final Context context) {
		this.context = context;
	}

	@Override
	public RealSort getSort() {
		if (sort == null) {
			sort = context.mkRealSort();
		}
		
		return sort;
	}

}
