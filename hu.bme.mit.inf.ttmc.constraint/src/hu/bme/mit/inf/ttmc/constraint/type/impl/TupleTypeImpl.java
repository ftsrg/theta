package hu.bme.mit.inf.ttmc.constraint.type.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;
import java.util.StringJoiner;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.inf.ttmc.constraint.type.TupleType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public class TupleTypeImpl extends AbstractType implements TupleType {
	
	private final ImmutableList<? extends Type> elemTypes;
	
	public TupleTypeImpl(final List<? extends Type> elemTypes) {
		this.elemTypes = ImmutableList.copyOf(checkNotNull(elemTypes));
	}
	
	@Override
	public List<? extends Type> getElemTypes() {
		return elemTypes;
	}
	
	@Override
	public String toString() {
		final String prefix = "Tuple(";
		final String suffix = ")";
		final StringJoiner sj = new StringJoiner(", ", prefix, suffix);
		for (Type type : elemTypes) {
			sj.add(type.toString());
		}
		return sj.toString();
	}

}
