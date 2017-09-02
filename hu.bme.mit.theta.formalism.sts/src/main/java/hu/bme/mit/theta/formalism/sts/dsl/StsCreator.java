package hu.bme.mit.theta.formalism.sts.dsl;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.formalism.sts.dsl.StsDslHelper.createExprList;
import static hu.bme.mit.theta.formalism.sts.dsl.StsDslHelper.resolveSts;

import java.util.List;

import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.core.model.Substitution;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslBaseVisitor;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.DefStsContext;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.RefStsContext;
import hu.bme.mit.theta.formalism.sts.dsl.gen.StsDslParser.StsContext;

final class StsCreator {

	private StsCreator() {
	}

	public static StsDefScope createSts(final Scope scope, final Substitution assignment, final StsContext stsContext) {
		return stsContext.accept(new StsCreatorVisitor(scope, assignment));
	}

	private static final class StsCreatorVisitor extends StsDslBaseVisitor<StsDefScope> {
		private final Scope scope;
		private final Substitution assignment;

		private StsCreatorVisitor(final Scope scope, final Substitution assignment) {
			this.scope = checkNotNull(scope);
			this.assignment = checkNotNull(assignment);
		}

		@Override
		public StsDefScope visitDefSts(final DefStsContext ctx) {
			final StsDefScope stsDefScope = StsDefScope.create(scope, assignment, ctx);
			return stsDefScope;
		}

		@Override
		public StsDefScope visitRefSts(final RefStsContext ctx) {
			final StsDeclSymbol symbol = resolveSts(scope, ctx.ref.getText());
			final List<Expr<?>> args = createExprList(scope, assignment, ctx.params);
			return symbol.instantiate(assignment, args);
		}
	}

}
