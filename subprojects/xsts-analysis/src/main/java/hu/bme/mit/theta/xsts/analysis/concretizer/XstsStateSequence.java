package hu.bme.mit.theta.xsts.analysis.concretizer;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.common.LispStringBuilder;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.xsts.XSTS;
import hu.bme.mit.theta.xsts.analysis.XstsState;
import hu.bme.mit.theta.xsts.dsl.TypeDecl;

import java.util.List;
import java.util.Optional;

import static com.google.common.base.Preconditions.*;

public final class XstsStateSequence {

	private final ImmutableList<XstsState<ExplState>> states;
	private final XSTS xsts;

	private XstsStateSequence(final List<XstsState<ExplState>> states, final XSTS xsts) {
		checkNotNull(states);
		checkArgument(!states.isEmpty(), "A trace must contain at least one state.");

		this.states = ImmutableList.copyOf(states);
		this.xsts = xsts;
	}

	public static XstsStateSequence of(final List<XstsState<ExplState>> states, final XSTS xsts) {
		return new XstsStateSequence(states, xsts);
	}

	public List<XstsState<ExplState>> getStates() {
		return states;
	}

	public XstsState<ExplState> getState(int index) {
		checkElementIndex(index, states.size());
		return states.get(index);
	}

	@Override
	public int hashCode() {
		return 31 * states.hashCode();
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof XstsStateSequence) {
			final XstsStateSequence that = (XstsStateSequence) obj;
			return this.states.equals(that.states);
		} else {
			return false;
		}
	}

	public int length() {
		return states.size() - 1;
	}

	@Override
	public String toString() {
		final LispStringBuilder sb = Utils.lispStringBuilder(getClass().getSimpleName()).body();
		for (int i = 0; i <= length(); i++) {
			XstsState<ExplState> state = states.get(i);
			sb.add(Utils.lispStringBuilder(XstsState.class.getSimpleName()).add(state.isInitialized() ? "post_init" : "pre_init").add(state.lastActionWasEnv() ? "last_env" : "last_internal").body().add(stateToString(state.getState())).toString());
		}
		return sb.toString();
	}

	public String stateToString(ExplState state) {
		final LispStringBuilder sb = Utils.lispStringBuilder(ExplState.class.getSimpleName()).body();
		for (VarDecl decl : xsts.getVars()) {
			Optional<LitExpr<?>> val = state.eval(decl);
			if (val.isPresent()) {
				if (xsts.getVarToType().containsKey(decl)) {
					TypeDecl type = xsts.getVarToType().get(decl);
					IntLitExpr intValue = (IntLitExpr) val.get();
					int index = type.getIntValues().indexOf(intValue.getValue());
					assert index != -1;
					sb.add(String.format("(%s %s)", decl.getName(), type.getLiterals().get(index)));
				} else {
					sb.add(String.format("(%s %s)", decl.getName(), val.get()));
				}
			}
		}
		return sb.toString();
	}
}
