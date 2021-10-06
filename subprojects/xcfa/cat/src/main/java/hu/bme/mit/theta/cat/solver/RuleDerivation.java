package hu.bme.mit.theta.cat.solver;

public abstract class RuleDerivation {
	private final String rule;

	public RuleDerivation(final String rule) {
		this.rule = rule;
	}

	public String getRule() {
		return rule;
	}

	public abstract <P, R> R accept(final RuleDerivationVisitor<P, R> derivationVisitor, P param);

	public abstract int getArity();

	public static class Element extends RuleDerivation {
		private final int arity;
		public Element(String rule, int arity) {
			super(rule);
			this.arity = arity;
		}

		public int getArity() {
			return arity;
		}

		@Override
		public <P, R> R accept(RuleDerivationVisitor<P, R> derivationVisitor, P param) {
			return derivationVisitor.visit(this, param);
		}
	}

	public static class Union extends RuleDerivation {
		private final RuleDerivation lhs;
		private final RuleDerivation rhs;

		public Union(String rule, RuleDerivation lhs, RuleDerivation rhs) {
			super(rule);
			this.lhs = lhs;
			this.rhs = rhs;
		}

		public RuleDerivation getLhs() {
			return lhs;
		}

		public RuleDerivation getRhs() {
			return rhs;
		}

		@Override
		public <P, R> R accept(RuleDerivationVisitor<P, R> derivationVisitor, P param) {
			return derivationVisitor.visit(this, param);
		}

		@Override
		public int getArity() {
			return lhs.getArity();
		}
	}

	public static class Intersection extends RuleDerivation {
		private final RuleDerivation lhs;
		private final RuleDerivation rhs;

		public Intersection(String rule, RuleDerivation lhs, RuleDerivation rhs) {
			super(rule);
			this.lhs = lhs;
			this.rhs = rhs;
		}

		public RuleDerivation getLhs() {
			return lhs;
		}

		public RuleDerivation getRhs() {
			return rhs;
		}

		@Override
		public int getArity() {
			return lhs.getArity();
		}

		@Override
		public <P, R> R accept(RuleDerivationVisitor<P, R> derivationVisitor, P param) {
			return derivationVisitor.visit(this, param);
		}
	}

	public static class Difference extends RuleDerivation {
		private final RuleDerivation lhs;
		private final RuleDerivation rhs;

		public Difference(String rule, RuleDerivation lhs, RuleDerivation rhs) {
			super(rule);
			this.lhs = lhs;
			this.rhs = rhs;
		}

		public RuleDerivation getLhs() {
			return lhs;
		}

		public RuleDerivation getRhs() {
			return rhs;
		}

		@Override
		public int getArity() {
			return lhs.getArity();
		}

		@Override
		public <P, R> R accept(RuleDerivationVisitor<P, R> derivationVisitor, P param) {
			return derivationVisitor.visit(this, param);
		}
	}

	public static class Inverse extends RuleDerivation {
		private final RuleDerivation lhs;

		public Inverse(String rule, RuleDerivation lhs) {
			super(rule);
			this.lhs = lhs;
		}

		public RuleDerivation getLhs() {
			return lhs;
		}

		@Override
		public int getArity() {
			return lhs.getArity();
		}

		@Override
		public <P, R> R accept(RuleDerivationVisitor<P, R> derivationVisitor, P param) {
			return derivationVisitor.visit(this, param);
		}
	}

	public static class Transitive extends RuleDerivation {
		private final Element lhs;

		public Transitive(String rule, Element lhs) {
			super(rule);
			this.lhs = lhs;
		}

		public Element getLhs() {
			return lhs;
		}

		@Override
		public <P, R> R accept(RuleDerivationVisitor<P, R> derivationVisitor, P param) {
			return derivationVisitor.visit(this, param);
		}

		@Override
		public int getArity() {
			return lhs.getArity();
		}
	}

	public static class SelfOrTransitive extends RuleDerivation {
		private final Element lhs;

		public SelfOrTransitive(String rule, Element lhs) {
			super(rule);
			this.lhs = lhs;
		}

		@Override
		public <P, R> R accept(RuleDerivationVisitor<P, R> derivationVisitor, P param) {
			return derivationVisitor.visit(this, param);
		}

		public Element getLhs() {
			return lhs;
		}

		@Override
		public int getArity() {
			return lhs.getArity();
		}
	}

	public static class Consecutive extends RuleDerivation {
		private final RuleDerivation lhs;
		private final RuleDerivation rhs;

		public Consecutive(String rule, RuleDerivation lhs, RuleDerivation rhs) {
			super(rule);
			this.lhs = lhs;
			this.rhs = rhs;
		}

		public RuleDerivation getLhs() {
			return lhs;
		}

		public RuleDerivation getRhs() {
			return rhs;
		}

		@Override
		public <P, R> R accept(RuleDerivationVisitor<P, R> derivationVisitor, P param) {
			return derivationVisitor.visit(this, param);
		}

		@Override
		public int getArity() {
			return lhs.getArity();
		}
	}

	public static class CartesianProduct extends RuleDerivation {
		private final RuleDerivation lhs;
		private final RuleDerivation rhs;

		public CartesianProduct(String rule, RuleDerivation lhs, RuleDerivation rhs) {
			super(rule);
			this.lhs = lhs;
			this.rhs = rhs;
		}

		public RuleDerivation getLhs() {
			return lhs;
		}

		public RuleDerivation getRhs() {
			return rhs;
		}

		@Override
		public <P, R> R accept(RuleDerivationVisitor<P, R> derivationVisitor, P param) {
			return derivationVisitor.visit(this, param);
		}

		@Override
		public int getArity() {
			return lhs.getArity() + rhs.getArity();
		}
	}
}
