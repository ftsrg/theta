package hu.bme.mit.inf.ttmc.analysis;

public interface Analysis<S extends State, P extends Precision> {
	
	public Domain<S> getDomain();
	
	public TransferRelation<S, P> getTransferRelation();
	
	public MergeOperator<S, P> getMergeOperator();
	public StopOperator<S, P> getStopOperator();
	public RefinementOperator<S, P> getRefinementOperator();
	
}