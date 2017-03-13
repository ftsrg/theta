package hu.bme.mit.theta.analysis.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.function.Function;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransferFunction;

public final class PrecMappingAnalysis<S extends State, A extends Action, PP extends Prec, PR extends Prec>
		implements Analysis<S, A, PP> {

	private final Domain<S> domain;
	private final InitFunction<S, PP> initFunction;
	private final TransferFunction<S, A, PP> transferFunction;

	private PrecMappingAnalysis(final Analysis<S, ? super A, ? super PR> analysis,
			final Function<? super PP, ? extends PR> mapping) {
		checkNotNull(analysis);
		checkNotNull(mapping);
		this.domain = analysis.getDomain();
		this.initFunction = PrecMappingInitFunction.create(analysis.getInitFunction(), mapping);
		this.transferFunction = PrecMappingTransferFunction.create(analysis.getTransferFunction(), mapping);
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
	public InitFunction<S, PP> getInitFunction() {
		return initFunction;
	}

	@Override
	public TransferFunction<S, A, PP> getTransferFunction() {
		return transferFunction;
	}

}
