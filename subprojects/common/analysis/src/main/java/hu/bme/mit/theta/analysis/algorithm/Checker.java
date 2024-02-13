package hu.bme.mit.theta.analysis.algorithm;

public interface Checker<W extends Witness, I> {

    Result<W> check(I input);

}
