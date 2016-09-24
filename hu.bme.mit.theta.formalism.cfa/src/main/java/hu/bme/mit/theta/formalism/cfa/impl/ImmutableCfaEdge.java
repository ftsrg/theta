package hu.bme.mit.theta.formalism.cfa.impl;

import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.formalism.cfa.CfaEdge;
import hu.bme.mit.theta.formalism.cfa.CfaLoc;
import hu.bme.mit.theta.formalism.cfa.impl.ImmutableCfaLoc.CFALocBuilder;

final class ImmutableCfaEdge implements CfaEdge {

	final CfaLoc source;
	final CfaLoc target;
	final List<Stmt> stmts;

	private ImmutableCfaEdge(final CFAEdgeBuilder builder) {
		builder.edge = this;

		source = builder.source.build();
		target = builder.target.build();
		stmts = ImmutableList.copyOf(builder.stmts);
	}


	@Override
	public CfaLoc getSource() {
		return source;
	}

	@Override
	public CfaLoc getTarget() {
		return target;
	}

	@Override
	public List<Stmt> getStmts() {
		return stmts;
	}

	////

	final static class CFAEdgeBuilder {

		private ImmutableCfaEdge edge;

		private CFALocBuilder source;
		private CFALocBuilder target;
		private List<Stmt> stmts;

		CFAEdgeBuilder(final List<Stmt> stmts) {
			this.stmts = stmts;
		}

		public ImmutableCfaEdge build() {
			if (edge == null) {
				new ImmutableCfaEdge(this);
			}

			return edge;
		}

		public void setSource(final CFALocBuilder source) {
			this.source = source;
		}

		public void setTarget(final CFALocBuilder target) {
			this.target = target;
		}
	}

}
