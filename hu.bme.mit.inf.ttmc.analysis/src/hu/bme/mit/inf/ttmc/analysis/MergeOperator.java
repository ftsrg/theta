package hu.bme.mit.inf.ttmc.analysis;

public interface MergeOperator<S extends State<S>> {

	public S merge(S state1, S state2);

}
