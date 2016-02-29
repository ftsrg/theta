package hu.bme.mit.inf.ttmc.analysis;

public interface Analysis<S extends State> {
	
	public Domain<S> getAbstractDomain();
	public TransferRelation<S> getTransferRelation();
	
}
