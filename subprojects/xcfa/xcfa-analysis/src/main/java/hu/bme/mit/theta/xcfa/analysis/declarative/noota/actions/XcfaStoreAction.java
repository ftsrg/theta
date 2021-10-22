package hu.bme.mit.theta.xcfa.analysis.declarative.noota.actions;

import com.google.common.collect.Streams;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;

import java.util.Collection;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.stmt.Stmts.Assume;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public class XcfaStoreAction extends XcfaDeclAction {
	private final XcfaLabel.StoreXcfaLabel<?> store;
	private final Object uniqeObject;
	private final VarDecl<?> ssaValue;
	private final Collection<Tuple2<Object, XcfaLabel.LoadXcfaLabel<?>>> writingTo;

	private XcfaStoreAction(XcfaLabel.StoreXcfaLabel<?> store, VarDecl<?> ssaValue, Collection<Tuple2<Object, XcfaLabel.LoadXcfaLabel<?>>> writingTo) {
		this.store = store;
		this.ssaValue = ssaValue;
		this.writingTo = List.copyOf(writingTo);
		this.uniqeObject = new Object();
	}

	public static XcfaStoreAction of(XcfaLabel.StoreXcfaLabel<?> store, VarDecl<?> ssaValue, Collection<Tuple2<Object, XcfaLabel.LoadXcfaLabel<?>>> writingTo) {
		return new XcfaStoreAction(store, ssaValue, writingTo);
	}

	@Override
	public List<Stmt> getStmts() {
		return Streams.concat(
					Stream.of(Assume(Eq(cast(ssaValue.getRef(), ssaValue.getType()), cast(store.getLocal().getRef(), ssaValue.getType())))),
					writingTo.stream().map(load -> (Stmt)Assign(cast(load.get2().getLocal(), load.get2().getLocal().getType()), cast(ssaValue.getRef(), load.get2().getLocal().getType()))))
				.collect(Collectors.toList());
	}

	public Collection<Tuple2<Object, XcfaLabel.LoadXcfaLabel<?>>> getWritingTo() {
		return writingTo;
	}

	public XcfaLabel.StoreXcfaLabel<?> getStore() {
		return store;
	}

	public VarDecl<?> getGlobal() {
		return store.getGlobal();
	}

	public VarDecl<?> getSsaValue() {
		return ssaValue;
	}

	public Object getUniqeObject() {
		return uniqeObject;
	}



	@Override
	public String toString() {
		return Utils.lispStringBuilder(this.getClass().getSimpleName()).addAll(List.of(store, ssaValue, writingTo)).toString();
	}
}
