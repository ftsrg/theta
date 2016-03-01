package hu.bme.mit.inf.ttmc.analysis.loc;

import hu.bme.mit.inf.ttmc.analysis.Analysis;
import hu.bme.mit.inf.ttmc.analysis.Domain;
import hu.bme.mit.inf.ttmc.analysis.MergeOperator;
import hu.bme.mit.inf.ttmc.analysis.StopOperator;
import hu.bme.mit.inf.ttmc.analysis.TransferRelation;
import hu.bme.mit.inf.ttmc.analysis.impl.SepMergeOperator;
import hu.bme.mit.inf.ttmc.analysis.impl.SepStopOperator;

public class LocAnalysis implements Analysis<LocState> {

	final Domain<LocState> domain;
	final TransferRelation<LocState> transferRelation;
	final MergeOperator<LocState> mergeOperator;
	final StopOperator<LocState> stopOperator;
	
	public LocAnalysis() {
		domain = new LocDomain();
		transferRelation = new LocTransferRelation();
		mergeOperator = new SepMergeOperator<LocState>();
		stopOperator = new SepStopOperator<>(domain);
	}
	
	@Override
	public Domain<LocState> getDomain() {
		return domain;
	}

	@Override
	public TransferRelation<LocState> getTransferRelation() {
		return transferRelation;
	}

	@Override
	public MergeOperator<LocState> getMergeOperator() {
		return mergeOperator;
	}

	@Override
	public StopOperator<LocState> getStopOperator() {
		return stopOperator;
	}

}
