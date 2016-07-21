package hu.bme.mit.inf.ttmc.formalism.common.decl.impl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.inf.ttmc.core.type.impl.Types.Rat;

import java.util.HashMap;
import java.util.Map;

import hu.bme.mit.inf.ttmc.core.type.RatType;
import hu.bme.mit.inf.ttmc.core.utils.DeclVisitor;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ClockDecl;
import hu.bme.mit.inf.ttmc.formalism.common.decl.IndexedConstDecl;
import hu.bme.mit.inf.ttmc.formalism.common.expr.ClockRefExpr;

class ClockDeclImpl implements ClockDecl {

	private static final int HASH_SEED = 8053;
	private static final String DECL_LABEL = "Clock";

	private final String name;
	private final ClockRefExpr ref;
	private final Map<Integer, IndexedConstDecl<RatType>> indexToConst;

	private volatile int hashCode = 0;

	ClockDeclImpl(final String name) {
		checkNotNull(name);
		checkArgument(name.length() > 0);
		this.name = name;
		ref = new ClockRefExprImpl(this);
		indexToConst = new HashMap<>();
	}

	@Override
	public String getName() {
		return name;
	}

	@Override
	public RatType getType() {
		return Rat();
	}

	@Override
	public ClockRefExpr getRef() {
		return ref;
	}

	@Override
	public IndexedConstDecl<RatType> getConstDecl(final int index) {
		checkArgument(index >= 0);
		IndexedConstDecl<RatType> constDecl = indexToConst.get(index);
		if (constDecl == null) {
			constDecl = new IndexedConstDeclImpl<>(this, index);
			indexToConst.put(index, constDecl);
		}
		return constDecl;
	}

	@Override
	public int compareTo(final ClockDecl that) {
		return this.getName().compareTo(that.getName());
	}

	@Override
	public <P, R> R accept(final DeclVisitor<? super P, ? extends R> visitor, final P param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + name.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		return this == obj;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(DECL_LABEL);
		sb.append("(");
		sb.append(name);
		sb.append(")");
		return sb.toString();
	}

}
