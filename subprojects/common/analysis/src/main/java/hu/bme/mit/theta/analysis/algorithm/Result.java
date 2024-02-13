package hu.bme.mit.theta.analysis.algorithm;

import java.util.Optional;

public interface Result<W extends Witness> {

    W getWitness();

    Optional<Statistics> getStats();

}
