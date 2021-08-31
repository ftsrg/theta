package hu.bme.mit.theta.analysis.expr;

import com.google.common.collect.Streams;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static com.google.common.base.Preconditions.checkArgument;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;

public class BasicMultiExprState<P, S extends ExprState> implements MultiExprState<P, S> {
	private final Map<P, S> states;

	private BasicMultiExprState(final Map<P, S> states) {
		this.states = Collections.unmodifiableMap(new LinkedHashMap<>(states));
	}

	public static <P, S extends ExprState> BasicMultiExprState<P, S> of(final Map<P, S> states) {
		return new BasicMultiExprState<>(states);
	}

	@Override
	public boolean isBottom() {
		return states.values().stream().anyMatch(State::isBottom);
	}

	@Override
	public Expr<BoolType> toExpr() {
		return And(states.values().stream().map(ExprState::toExpr).collect(Collectors.toSet()));
	}

	@Override
	public BasicMultiExprState<P, S> add(P p, S s) {
		return BasicMultiExprState.of(Streams.concat(states.entrySet().stream(), Stream.of(Map.entry(p, s))).collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue)));
	}

	@Override
	public BasicMultiExprState<P, S> remove(P p) {
		return BasicMultiExprState.of(states.entrySet().stream().filter(psEntry -> !psEntry.getKey().equals(p)).collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue)));
	}

	@Override
	public BasicMultiExprState<P, S> update(P p, S s) {
		checkArgument(states.containsKey(p), "Cannot update non-existant entry!");
		return BasicMultiExprState.of(Streams.concat(states.entrySet().stream(), Stream.of(Map.entry(p, s))).collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue, (s1, s2) -> s2)));
	}

	@Override
	public Map<P, S> getStates() {
		return states;
	}

	@Override
	public String toString() {
		return Utils.lispStringBuilder(getClass().getSimpleName()).body().addAll(states.entrySet().stream().map(psEntry -> Utils.lispStringBuilder().add(psEntry.getKey()).add(psEntry.getValue()))).toString();
	}
}
