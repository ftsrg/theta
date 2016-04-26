package hu.bme.mit.inf.ttmc.analysis;

public interface Domain<S extends State<S>> {

	public S join(S state1, S state2);

	public boolean isLeq(S state1, S state2);

}
