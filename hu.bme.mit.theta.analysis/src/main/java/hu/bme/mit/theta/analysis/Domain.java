package hu.bme.mit.theta.analysis;

public interface Domain<S extends State> {

	boolean isTop(S state);

	boolean isBottom(S state);

	boolean isLeq(S state1, S state2);

}
