package hu.bme.mit.theta.cat.solver;

import hu.bme.mit.theta.common.Tuple2;

import java.util.Collection;

public interface MemoryModelSolver<Store, Load> {
	Collection<? extends Collection<Tuple2<Store, Load>>> getAllRf();
//	Optional<? extends Collection<Tuple2<Store, Load>>> getNextRf();
}
