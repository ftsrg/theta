package hu.bme.mit.theta.formalism.xta.dsl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.decl.impl.Decls;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.formalism.ta.decl.impl.Decls2;
import hu.bme.mit.theta.formalism.xta.dsl.gen.XtaDslParser.TypeContext;
import hu.bme.mit.theta.formalism.xta.dsl.gen.XtaDslParser.VariableIdContext;
import hu.bme.mit.theta.formalism.xta.utils.ClockType;
import hu.bme.mit.theta.formalism.xta.utils.RangeType;

final class XtaVariableSymbol implements Symbol {

	private final String name;
	private final boolean constant;

	private final XtaType type;
	private final XtaInitialiser initialiser;

	public XtaVariableSymbol(final Scope scope, final TypeContext typeContext,
			final VariableIdContext variableIdcontext) {
		checkNotNull(typeContext);
		checkNotNull(variableIdcontext);
		name = variableIdcontext.fArrayId.fId.getText();
		constant = (typeContext.fTypePrefix.fConst != null);
		type = new XtaType(scope, typeContext, variableIdcontext.fArrayId.fArrayIndexes);
		initialiser = variableIdcontext.fInitialiser != null ? new XtaInitialiser(scope, variableIdcontext.fInitialiser)
				: null;

		checkArgument(constant || initialiser == null, "Initialisers are only supported for constants");
	}

	@Override
	public String getName() {
		return name;
	}

	public boolean isConstant() {
		return constant;
	}

	public Expr<?> instantiate(final String prefix, final Environment env) {
		final Type varType = type.instantiate(env);
		checkArgument(!(varType instanceof RangeType));

		if (constant) {
			final Expr<?> expr = initialiser.instantiate(varType, env);
			return expr;
		} else {
			final VarDecl<?> varDecl;
			if (varType instanceof ClockType) {
				varDecl = Decls2.Clock(prefix + name);
			} else {
				varDecl = Decls.Var(prefix + name, varType);
			}
			final Expr<?> varRef = varDecl.getRef();
			return varRef;
		}
	}

}
