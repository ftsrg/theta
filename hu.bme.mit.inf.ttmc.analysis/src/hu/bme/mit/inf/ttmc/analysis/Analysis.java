package hu.bme.mit.inf.ttmc.analysis;

public interface Analysis<S extends AbstractState> {
	
	public AbstractDomain<S> getAbstractDomain();
	public TransferRelation<S> getTransferRelation();
	
}
