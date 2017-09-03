package hu.bme.mit.theta.analysis.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.function.Function;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransferFunc;

public final class PrecMappingAnalysis<S extends State, A extends Action, PP extends Prec, PR extends Prec>
		implements Analysis<S, A, PP> {

	private final Domain<S> domain;
	private final InitFunc<S, PP> initFunc;
	private final TransferFunc<S, A, PP> transferFunc;

	private PrecMappingAnalysis(final Analysis<S, ? super A, ? super PR> analysis,
			final Function<? super PP, ? extends PR> mapping) {
		checkNotNull(analysis);
		checkNotNull(mapping);
		this.domain = analysis.getDomain();
		this.initFunc = PrecMappingInitFunc.create(analysis.getInitFunc(), mapping);
		this.transferFunc = PrecMappingTransferFunc.create(analysis.getTransferFunc(), mapping);
	}

	public static <S extends State, A extends Action, PP extends Prec, PR extends Prec> PrecMappingAnalysis<S, A, PP, PR> create(
			final Analysis<S, ? super A, ? super PR> analysis, final Function<? super PP, ? extends PR> mapping) {
		return new PrecMappingAnalysis<>(analysis, mapping);
	}

	@Override
	public Domain<S> getDomain() {
		return domain;
	}

	@Override
	public InitFunc<S, PP> getInitFunc() {
		return initFunc;
	}

	@Override
	public TransferFunc<S, A, PP> getTransferFunc() {
		return transferFunc;
	}

}
