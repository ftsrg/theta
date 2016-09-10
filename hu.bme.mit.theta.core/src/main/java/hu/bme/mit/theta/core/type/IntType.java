package hu.bme.mit.theta.core.type;

import hu.bme.mit.theta.core.type.closure.ClosedUnderAdd;
import hu.bme.mit.theta.core.type.closure.ClosedUnderMul;
import hu.bme.mit.theta.core.type.closure.ClosedUnderNeg;
import hu.bme.mit.theta.core.type.closure.ClosedUnderSub;

public interface IntType extends RatType, ClosedUnderNeg, ClosedUnderSub, ClosedUnderAdd, ClosedUnderMul {

	
}
