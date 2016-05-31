package hu.bme.mit.inf.ttmc.analysis;

public interface SystemAbstraction<S extends State, P extends Precision> {

	public InitFunction<S, P> getInitFunction();

	public TransferFunction<S, P> getTransferFunction();

}
