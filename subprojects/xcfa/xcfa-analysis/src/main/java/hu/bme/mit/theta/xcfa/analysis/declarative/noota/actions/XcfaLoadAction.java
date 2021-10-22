package hu.bme.mit.theta.xcfa.analysis.declarative.noota.actions;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;

import java.util.List;
import java.util.Optional;

import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.stmt.Stmts.Assume;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public class XcfaLoadAction extends XcfaDeclAction {
	private final XcfaLabel.LoadXcfaLabel<?> load;
	private final Object uniqeObject;
	private final VarDecl<?> ssaValue;
	private final Optional<Tuple2<Object, VarDecl<?>>> readingFrom;

	private XcfaLoadAction(XcfaLabel.LoadXcfaLabel<?> load, VarDecl<?> ssaValue, Optional<Tuple2<Object, VarDecl<?>>> readingFrom) {
		this.load = load;
		this.ssaValue = ssaValue;
		this.readingFrom = readingFrom;
		uniqeObject = new Object();
	}

	public static XcfaLoadAction of(XcfaLabel.LoadXcfaLabel<?> load, VarDecl<?> ssaValue, Tuple2<Object, VarDecl<?>> store) {
		return new XcfaLoadAction(load, ssaValue, Optional.of(store));
	}

	public static XcfaLoadAction of(XcfaLabel.LoadXcfaLabel<?> load, VarDecl<?> ssaValue) {
		return new XcfaLoadAction(load, ssaValue, Optional.empty());
	}

	// This is buggy when the variable is not being tracked
	@Override
	public List<Stmt> getStmts() {
		final Stmt assume = Assume(Eq(cast(load.getLocal().getRef(), load.getLocal().getType()), cast(ssaValue.getRef(), load.getLocal().getType())));
		return readingFrom.map(store -> List.of(
					Assign(cast(load.getLocal(), load.getLocal().getType()), cast(readingFrom.get().get2().getRef(), load.getLocal().getType())),
					assume
				))
				.orElse(List.of(assume));
	}

	public XcfaLabel.LoadXcfaLabel<?> getLoad() {
		return load;
	}

	public Optional<Tuple2<Object, VarDecl<?>>> getReadingFrom() {
		return readingFrom;
	}

	public VarDecl<?> getGlobal() {
		return load.getGlobal();
	}

	public Object getUniqeObject() {
		return uniqeObject;
	}

	public VarDecl<?> getSsaValue() {
		return ssaValue;
	}

	@Override
	public String toString() {
		return Utils.lispStringBuilder(this.getClass().getSimpleName()).addAll(List.of(load, ssaValue, readingFrom)).toString();
	}
}
