package hu.bme.mit.inf.ttmc.formalism.sts.impl;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.stream.Collectors;

import hu.bme.mit.inf.ttmc.core.Model;
import hu.bme.mit.inf.ttmc.core.expr.AndExpr;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.core.utils.impl.ExprUtils;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.FoldVisitor;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.UnfoldVisitor;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.VarMap;

class STSUnrollerImpl {
	private final STS sts;
	private final UnfoldVisitor ufVisitor;
	private final FoldVisitor fVisitor;
	private final VarMap varMap;

	public STSUnrollerImpl(final STS sts) {
		this.sts = sts;
		varMap = new VarMap();
		ufVisitor = new UnfoldVisitor(varMap);
		fVisitor = new FoldVisitor(varMap);
	}

	public Expr<? extends BoolType> unroll(final Expr<? extends BoolType> expr, final int i) {
		return ExprUtils.cast(expr.accept(ufVisitor, i), BoolType.class);
	}

	public Collection<Expr<? extends BoolType>> init(final int i) {
		return sts.getInit().stream().map(e -> unroll(e, i)).collect(Collectors.toSet());
	}

	public Collection<Expr<? extends BoolType>> trans(final int i) {
		return sts.getTrans().stream().map(e -> unroll(e, i)).collect(Collectors.toSet());
	}

	public Collection<Expr<? extends BoolType>> inv(final int i) {
		return sts.getInvar().stream().map(e -> unroll(e, i)).collect(Collectors.toSet());
	}

	public Expr<? extends BoolType> prop(final int i) {
		return unroll(sts.getProp(), i);
	}

	public AndExpr getConcreteState(final Model model, final int i, final Collection<VarDecl<? extends Type>> variables) {

		final List<Expr<? extends BoolType>> ops = new ArrayList<>(variables.size());

		for (final VarDecl<? extends Type> varDecl : variables) {
			Expr<? extends Type> value = null;
			try {
				value = model.eval(varMap.getConstDecl(varDecl, i)).get();
			} catch (final Exception ex) {
				value = varDecl.getType().getAny();
			}
			ops.add(Exprs.Eq(varDecl.getRef(), value));
		}

		return Exprs.And(ops);
	}

	public List<AndExpr> extractTrace(final Model model, final int length, final Collection<VarDecl<? extends Type>> variables) {

		final List<AndExpr> trace = new ArrayList<>(length);
		for (int i = 0; i < length; ++i)
			trace.add(getConcreteState(model, i, variables));
		return trace;
	}

	public Expr<? extends BoolType> foldin(final Expr<? extends BoolType> expr, final int i) {
		return ExprUtils.cast(expr.accept(fVisitor, i), BoolType.class);
	}

}
