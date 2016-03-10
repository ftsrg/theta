package hu.bme.mit.inf.ttmc.common.impl;

import java.util.List;
import java.util.StringJoiner;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.inf.ttmc.common.Tuple;

public abstract class AbstractTuple implements Tuple {

	private volatile int hashCode = 0;
	
	private final List<Object> elems;
	
	public AbstractTuple(Object... elems) {
		this.elems = ImmutableList.of(elems);
	}
	
	@Override
	public int getArity() {
		return elems.size();
	}
	
	@Override
	public List<Object> getElems() {
		return elems;
	}
	
	@Override
	public int hashCode() {
		if (hashCode == 0) {
			hashCode = getArity();
			hashCode = 31 * hashCode + elems.hashCode();
		}
		return hashCode;
	}
	
	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj == null) {
			return false;
		} else if (this.getClass() == obj.getClass()) {
			final AbstractTuple that = (AbstractTuple) obj;
			return this.elems.equals(that.elems);
		} else {
			return false;
		}
	}
	
	@Override
	public String toString() {
		final StringJoiner sj = new StringJoiner(", ", "(", ")");
		for (Object elem : elems) {
			sj.add(elem.toString());
		}
		return sj.toString();
	}

}
