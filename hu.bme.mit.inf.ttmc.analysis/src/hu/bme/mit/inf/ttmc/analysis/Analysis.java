package hu.bme.mit.inf.ttmc.analysis;

public interface Analysis<S extends State> {
	
	public Domain<S> getDomain();
	public TransferRelation<S> getTransferRelation();
	
}
