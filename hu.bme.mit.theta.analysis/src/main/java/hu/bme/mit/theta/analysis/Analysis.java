package hu.bme.mit.theta.analysis;

public interface Analysis<S extends State, A extends Action, P extends Precision> {

	Domain<S> getDomain();

	InitFunction<S, P> getInitFunction();

	TransferFunction<S, A, P> getTransferFunction();

}
