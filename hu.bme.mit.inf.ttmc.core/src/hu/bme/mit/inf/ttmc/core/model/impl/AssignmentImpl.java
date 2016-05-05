package hu.bme.mit.inf.ttmc.core.model.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.inf.ttmc.core.decl.Decl;
import hu.bme.mit.inf.ttmc.core.expr.LitExpr;
import hu.bme.mit.inf.ttmc.core.model.Assignment;
import hu.bme.mit.inf.ttmc.core.type.Type;

public final class AssignmentImpl implements Assignment {

	private final Collection<Decl<?, ?>> decls;
	private final Map<Decl<?, ?>, LitExpr<?>> declToExpr;

	private static final Assignment EMPTY;

	static {
		EMPTY = new AssignmentImpl();
	}

	public static Assignment empty() {
		return EMPTY;
	}

	public AssignmentImpl() {
		this(new HashMap<>());
	}

	public AssignmentImpl(final Map<Decl<?, ?>, LitExpr<?>> constToExpr) {
		this.declToExpr = new HashMap<>(constToExpr);
		this.decls = ImmutableList.copyOf(constToExpr.keySet());
	}

	@Override
	public <DeclType extends Type, DeclKind extends Decl<DeclType, DeclKind>> Optional<LitExpr<DeclType>> eval(final Decl<DeclType, DeclKind> decl) {
		checkNotNull(decl);

		if (declToExpr.containsKey(decl)) {

			@SuppressWarnings("unchecked")
			final LitExpr<DeclType> val = (LitExpr<DeclType>) declToExpr.get(decl);
			return Optional.of(val);
		}

		return Optional.empty();
	}

	@Override
	public Collection<? extends Decl<?, ?>> getDecls() {
		return decls;
	}

}
