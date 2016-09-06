package hu.bme.mit.inf.theta.analysis;

public interface Analysis<S extends State, A extends Action, P extends Precision> {

	public Domain<S> getDomain();

	public InitFunction<S, P> getInitFunction();

	public TransferFunction<S, A, P> getTransferFunction();

	public ActionFunction<? super S, ? extends A> getActionFunction();

}
