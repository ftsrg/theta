package hu.bme.mit.inf.ttmc.analysis;

public interface State<S extends State<S>> {

	public S join(S state);

	public boolean isLeq(S state);

}
