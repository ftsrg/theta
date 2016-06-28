package hu.bme.mit.inf.ttmc.analysis;

@FunctionalInterface
public interface TargetPredicate<S extends State> {

	public boolean isTargetState(S state);

}
