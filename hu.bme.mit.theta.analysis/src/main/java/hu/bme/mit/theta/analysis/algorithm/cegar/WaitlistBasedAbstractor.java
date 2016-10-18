package hu.bme.mit.theta.analysis.algorithm.cegar;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import java.util.function.Predicate;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgBuilder;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.algorithm.Waitlist;

public class WaitlistBasedAbstractor<S extends State, A extends Action, P extends Precision>
		implements Abstractor<S, A, P> {

	private final Waitlist<ArgNode<S, A>> waitlist;
	private final ArgBuilder<S, A, P> argBuilder;

	private ARG<S, A> arg;

	private WaitlistBasedAbstractor(final Analysis<S, A, P> analysis, final Predicate<? super S> target,
			final Waitlist<ArgNode<S, A>> waitlist) {
		checkNotNull(analysis);
		checkNotNull(target);
		this.waitlist = checkNotNull(waitlist);
		argBuilder = ArgBuilder.create(analysis, target);
	}

	public static <S extends State, A extends Action, P extends Precision> WaitlistBasedAbstractor<S, A, P> create(
			final Analysis<S, A, P> analysis, final Predicate<? super S> target,
			final Waitlist<ArgNode<S, A>> waitlist) {
		return new WaitlistBasedAbstractor<>(analysis, target, waitlist);
	}

	@Override
	public ARG<S, A> getARG() {
		checkState(arg != null);
		return arg;
	}

	@Override
	public void init(final P precision) {
		arg = ARG.create();
		argBuilder.init(arg, precision);
		waitlist.clear();
	}

	@Override
	public void check(final P precision) {
		checkState(arg != null);

		waitlist.clear();
		waitlist.addAll(arg.getLeafNodes());
		while (!waitlist.isEmpty()) {
			final ArgNode<S, A> node = waitlist.remove();

			if (node.isTarget()) {
				return;
			}

			argBuilder.close(node);
			if (!node.isCovered()) {
				argBuilder.expand(node, precision);
				waitlist.addAll(node.getSuccNodes());
			}
		}
	}

	@Override
	public AbstractorStatus getStatus() {
		checkState(arg != null);
		return arg.getTargetNodes().size() == 0 ? AbstractorStatus.OK : AbstractorStatus.CEX;
	}

}
