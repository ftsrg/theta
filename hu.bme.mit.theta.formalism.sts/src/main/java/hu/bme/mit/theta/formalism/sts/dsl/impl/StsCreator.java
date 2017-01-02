package hu.bme.mit.theta.formalism.sts.dsl.impl;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.utils.impl.ExprUtils.simplify;
import static hu.bme.mit.theta.formalism.sts.dsl.impl.StsDslHelper.createBoolExpr;
import static hu.bme.mit.theta.formalism.sts.dsl.impl.StsDslHelper.createConstDefs;
import static hu.bme.mit.theta.formalism.sts.dsl.impl.StsDslHelper.declareConstDecls;
import static hu.bme.mit.theta.formalism.sts.dsl.impl.StsDslHelper.declareVarDecls;
import static hu.bme.mit.theta.formalism.sts.dsl.impl.StsDslHelper.resolveSts;
import static java.util.stream.Collectors.toList;

import java.util.List;

import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.model.Assignment;
import hu.bme.mit.theta.core.model.impl.AssignmentImpl;
import hu.bme.mit.theta.core.model.impl.NestedAssignment;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslBaseVisitor;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.DefStsContext;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.InitConstrContext;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.InvarConstrContext;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.RefStsContext;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.StsContext;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.TransConstrContext;
import hu.bme.mit.theta.formalism.sts.impl.StsImpl;
import hu.bme.mit.theta.formalism.sts.impl.StsImpl.Builder;

final class StsCreator {

	private StsCreator() {
	}

	public static StsCreationResult createSts(final StsContext stsContext, final Scope2 scope,
			final Assignment assignment) {
		return stsContext.accept(new StsCreatorVisitor(scope, assignment));
	}

	public static StsCreationResult createSts(final StsSymbol symbol, final Assignment assignment) {
		return createSts(symbol.getStsCtx(), symbol, assignment);
	}

	public static final class StsCreationResult {
		private final Scope2 scope;
		private final StsImpl.Builder builder;

		public StsCreationResult(final Scope2 scope, final StsImpl.Builder builder) {
			this.scope = checkNotNull(scope);
			this.builder = checkNotNull(builder);
		}

		public Scope2 getScope() {
			return scope;
		}

		public StsImpl.Builder getBuilder() {
			return builder;
		}
	}

	private static final class StsCreatorVisitor extends StsDslBaseVisitor<StsCreationResult> {

		private Scope2 currentScope;
		private Assignment currentAssignment;

		private StsCreatorVisitor(final Scope2 scope, final Assignment assignment) {
			currentScope = checkNotNull(scope);
			currentAssignment = checkNotNull(assignment);
		}

		////

		@Override
		public StsCreationResult visitDefSts(final DefStsContext ctx) {
			final StsImpl.Builder stsBuilder = new StsImpl.Builder();

			push();

			declareConstDecls(currentScope, ctx.constDecls);
			declareVarDecls(currentScope, ctx.varDecls);

			final Assignment constAssignment = createConstDefs(currentScope, currentAssignment, ctx.constDecls);
			currentAssignment = NestedAssignment.create(currentAssignment, constAssignment);

			createInvarConstrs(stsBuilder, ctx.invarConstrs);
			createInitConstrs(stsBuilder, ctx.initConstrs);
			createTransConstrs(stsBuilder, ctx.transConstrs);

			final StsCreationResult result = new StsCreationResult(currentScope, stsBuilder);

			pop();

			return result;
		}

		private void createInvarConstrs(final Builder stsBuilder,
				final List<? extends InvarConstrContext> invarConstrCtxs) {
			invarConstrCtxs.forEach(ctx -> createInvarConstr(stsBuilder, ctx));
		}

		private void createInvarConstr(final Builder stsBuilder, final InvarConstrContext invarConstrCtx) {
			final Expr<? extends BoolType> cond = createBoolExpr(currentScope, currentAssignment, invarConstrCtx.cond);
			stsBuilder.addInvar(cond);
		}

		private void createInitConstrs(final Builder stsBuilder,
				final List<? extends InitConstrContext> initConstrCtxs) {
			initConstrCtxs.forEach(ctx -> createInitConstr(stsBuilder, ctx));
		}

		private void createInitConstr(final Builder stsBuilder, final InitConstrContext initConstrCtx) {
			final Expr<? extends BoolType> cond = createBoolExpr(currentScope, currentAssignment, initConstrCtx.cond);
			stsBuilder.addInit(cond);
		}

		private void createTransConstrs(final Builder stsBuilder,
				final List<? extends TransConstrContext> transConstrCtxs) {
			transConstrCtxs.forEach(ctx -> createTransConstr(stsBuilder, ctx));
		}

		private void createTransConstr(final Builder stsBuilder, final TransConstrContext transConstrCtx) {
			final Expr<? extends BoolType> cond = createBoolExpr(currentScope, currentAssignment, transConstrCtx.cond);
			stsBuilder.addTrans(cond);
		}

		private void push() {
			currentScope = new BasicScope2(currentScope);
		}

		private void pop() {
			checkState(currentScope.enclosingScope().isPresent());
			currentScope = currentScope.enclosingScope().get();
		}

		////

		@Override
		public StsCreationResult visitRefSts(final RefStsContext ctx) {
			final StsSymbol symbol = resolveSts(currentScope, ctx.ref.getText());
			final List<ParamDecl<?>> paramDecls = symbol.getParamDecls();

			final List<Expr<?>> paramsToEval = StsDslHelper.createExprList(currentScope, currentAssignment, ctx.params);
			final List<Expr<?>> params = simplifyAll(paramsToEval, currentAssignment);
			final Assignment paramAssignment = new AssignmentImpl(paramDecls, params);
			final Assignment newAssignment = NestedAssignment.create(currentAssignment, paramAssignment);

			final StsCreationResult result = createSts(symbol, newAssignment);

			return result;
		}

		private static List<Expr<?>> simplifyAll(final List<? extends Expr<?>> exprs, final Assignment assignment) {
			return exprs.stream().map(e -> (Expr<?>) simplify(e, assignment)).collect(toList());
		}

	}

}
