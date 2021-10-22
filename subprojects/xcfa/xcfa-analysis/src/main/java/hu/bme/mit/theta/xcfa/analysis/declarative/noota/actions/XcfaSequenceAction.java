package hu.bme.mit.theta.xcfa.analysis.declarative.noota.actions;

import com.google.common.collect.Streams;
import hu.bme.mit.theta.core.stmt.Stmt;

import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class XcfaSequenceAction extends XcfaDeclAction{
	private final List<XcfaDeclAction> actions;

	private XcfaSequenceAction(final List<XcfaDeclAction> actions) {
		this.actions = List.copyOf(actions);
	}

	public static XcfaSequenceAction of(final List<XcfaDeclAction> actions) {
		return new XcfaSequenceAction(actions);
	}

	public static XcfaSequenceAction of(XcfaDeclAction ...actions) {
		return new XcfaSequenceAction(Arrays.asList(actions));
	}

	@Override
	public List<Stmt> getStmts() {
		return actions.stream().map(a -> a.getStmts().stream()).reduce(Streams::concat).orElse(Stream.empty()).collect(Collectors.toList());
	}

	public List<XcfaDeclAction> getActions() {
		return actions;
	}



	@Override
	public String toString() {
		return getStmts().toString();
//		return Utils.lispStringBuilder(this.getClass().getSimpleName()).addAll(actions).toString();
	}
}
