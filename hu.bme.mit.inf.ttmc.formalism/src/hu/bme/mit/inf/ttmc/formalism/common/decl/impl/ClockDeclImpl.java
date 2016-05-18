package hu.bme.mit.inf.ttmc.formalism.common.decl.impl;

import static com.google.common.base.Preconditions.checkArgument;
import static hu.bme.mit.inf.ttmc.core.type.impl.Types.Rat;

import java.util.HashMap;
import java.util.Map;

import hu.bme.mit.inf.ttmc.core.decl.impl.AbstractDecl;
import hu.bme.mit.inf.ttmc.core.type.RatType;
import hu.bme.mit.inf.ttmc.core.utils.DeclVisitor;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ClockDecl;
import hu.bme.mit.inf.ttmc.formalism.common.decl.IndexedConstDecl;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.expr.ClockRefExpr;

class ClockDeclImpl extends AbstractDecl<RatType, VarDecl<RatType>> implements ClockDecl {

	private static final int HASH_SEED = 8053;
	private static final String DECL_LABEL = "Clock";

	private final ClockRefExpr ref;
	private final Map<Integer, IndexedConstDecl<RatType>> indexToConst;

	ClockDeclImpl(final String name) {
		super(name, Rat());
		ref = new ClockRefExprImpl(this);
		indexToConst = new HashMap<>();
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
	public <P, R> R accept(final DeclVisitor<? super P, ? extends R> visitor, final P param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public int compareTo(final ClockDecl that) {
		return this.getName().compareTo(that.getName());
	}

	@Override
	protected int getHashSeed() {
		return HASH_SEED;
	}

	@Override
	protected String getDeclLabel() {
		return DECL_LABEL;
	}

}
