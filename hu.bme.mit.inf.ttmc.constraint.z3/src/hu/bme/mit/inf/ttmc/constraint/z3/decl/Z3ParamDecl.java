package hu.bme.mit.inf.ttmc.constraint.z3.decl;

import com.microsoft.z3.Context;
import com.microsoft.z3.Sort;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.decl.defaults.AbstractParamDecl;
import hu.bme.mit.inf.ttmc.constraint.type.FuncType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.z3.type.Z3Type;

public final class Z3ParamDecl<DeclType extends Type> extends AbstractParamDecl<DeclType> implements Z3Decl<DeclType> {

	private final Context context;

	private volatile com.microsoft.z3.FuncDecl symbol;

	public Z3ParamDecl(final ConstraintManager manager, final String name, final DeclType type, final Context context) {
		super(manager, name, type);
		this.context = context;
	}

	@Override
	public com.microsoft.z3.FuncDecl getSymbol() {
		if (symbol == null) {
			final Type type = getType();
			if (type instanceof FuncType<?, ?>) {
				throw new UnsupportedOperationException("Only simple types are supported");
			} else {
				final Z3Type z3type = (Z3Type) getType();
				final Sort sort = z3type.getSort();
				symbol = context.mkConstDecl(getName(), sort);
			}
		}

		return symbol;
	}

}
