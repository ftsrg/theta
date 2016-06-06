package hu.bme.mit.inf.ttmc.analysis;

@FunctionalInterface
public interface TargetPredicate<S extends State, Target> {

	public boolean isTargetState(S state, Target target);

}
