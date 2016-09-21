package hu.bme.mit.theta.analysis;

public interface Domain<S extends State> {

	public boolean isTop(S state);

	public boolean isBottom(S state);

	public boolean isLeq(S state1, S state2);

}
