package hu.bme.mit.inf.ttmc.analysis;

public interface AbstractDomain<S extends AbstractState> {
	
	public S getTop();
	public S getBottom();
	public S join(S state1, S state2);
	public S meet(S state1, S state2);
	public boolean isLeq(S state1, S state2);
	
}