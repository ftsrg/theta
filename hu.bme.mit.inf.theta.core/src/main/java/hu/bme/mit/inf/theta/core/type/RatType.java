package hu.bme.mit.inf.theta.core.type;

import hu.bme.mit.inf.theta.core.type.closure.ClosedUnderAdd;
import hu.bme.mit.inf.theta.core.type.closure.ClosedUnderMul;
import hu.bme.mit.inf.theta.core.type.closure.ClosedUnderNeg;
import hu.bme.mit.inf.theta.core.type.closure.ClosedUnderSub;

public interface RatType extends BaseType, ClosedUnderNeg, ClosedUnderSub, ClosedUnderAdd, ClosedUnderMul {

}
