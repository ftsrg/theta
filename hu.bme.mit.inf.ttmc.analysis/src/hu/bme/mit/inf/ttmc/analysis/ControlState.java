package hu.bme.mit.inf.ttmc.analysis;

import java.util.Collection;

public interface ControlState<T extends Action> extends State {

	public Collection<? extends T> getActions();

}
