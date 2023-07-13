package hu.bme.mit.theta.analysis;

import java.util.Collection;

public interface InvTransFunc<S extends State, A extends Action, P extends Prec> {

    Collection<? extends S> getPreStates(S state, A action, P prec);

}
