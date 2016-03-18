package hu.bme.mit.inf.ttmc.formalism.sts.impl;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

import hu.bme.mit.inf.ttmc.constraint.expr.AndExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.solver.Model;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.ExprUtils;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;
import hu.bme.mit.inf.ttmc.formalism.sts.STSUnroller;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.FoldVisitor;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.UnfoldVisitor;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.VarMap;

public class STSUnrollerImpl implements STSUnroller {
	private final STS sts;
	private final STSManager manager;
	private final UnfoldVisitor ufVisitor;
	private final FoldVisitor fVisitor;
	private final VarMap varMap;

	public STSUnrollerImpl(final STS sts, final STSManager manager) {
		this.sts = sts;
		this.manager = manager;
		varMap = new VarMap(manager.getDeclFactory());
		ufVisitor = new UnfoldVisitor(varMap, manager.getExprFactory());
		fVisitor = new FoldVisitor(varMap, manager.getExprFactory());
	}

	@Override
	public Expr<? extends BoolType> unroll(final Expr<? extends BoolType> expr, final int i) {
		return ExprUtils.cast(expr.accept(ufVisitor, i), BoolType.class);
	}

	@Override
	public Collection<Expr<? extends BoolType>> init(final int i) {
		return sts.getInit().stream().map(e -> unroll(e, i)).collect(Collectors.toSet());
	}

	@Override
	public Collection<Expr<? extends BoolType>> trans(final int i) {
		return sts.getTrans().stream().map(e -> unroll(e, i)).collect(Collectors.toSet());
	}

	@Override
	public Collection<Expr<? extends BoolType>> inv(final int i) {
		return sts.getInvar().stream().map(e -> unroll(e, i)).collect(Collectors.toSet());
	}

	@Override
	public Expr<? extends BoolType> prop(final int i) {
		return unroll(sts.getProp(), i);
	}

	@Override
	public AndExpr getConcreteState(final Model model, final int i) {
		return getConcreteState(model, i, sts.getVars());
	}

	@Override
	public AndExpr getConcreteState(final Model model, final int i,
			final Collection<VarDecl<? extends Type>> variables) {
		final List<Expr<? extends BoolType>> ops = new ArrayList<>(variables.size());

		for (final VarDecl<? extends Type> varDecl : variables) {
			Expr<? extends Type> value = null;
			final Optional<?> eval = model.eval(varMap.getConstDecl(varDecl, i));
			if (eval.isPresent())
				value = (Expr<? extends Type>) eval.get();
			else
				throw new UnsupportedOperationException("TODO: AnyVal");
			ops.add(manager.getExprFactory().Eq(varDecl.getRef(), value));
		}

		return manager.getExprFactory().And(ops);
	}

	@Override
	public List<AndExpr> extractTrace(final Model model, final int length) {
		return extractTrace(model, length, sts.getVars());
	}

	@Override
	public List<AndExpr> extractTrace(final Model model, final int length,
			final Collection<VarDecl<? extends Type>> variables) {
		final List<AndExpr> trace = new ArrayList<>(length);
		for (int i = 0; i < length; ++i)
			trace.add(getConcreteState(model, i, variables));
		return trace;
	}

	@Override
	public Expr<? extends BoolType> foldin(final Expr<? extends BoolType> expr, final int i) {
		return ExprUtils.cast(expr.accept(fVisitor, i), BoolType.class);
	}

}
