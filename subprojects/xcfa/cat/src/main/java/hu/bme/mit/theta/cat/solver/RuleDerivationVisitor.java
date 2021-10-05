package hu.bme.mit.theta.cat.solver;

public interface RuleDerivationVisitor<P, R> {
	R visit(RuleDerivation.Element derivation, P param);

	R visit(RuleDerivation.Union derivation, P param);

	R visit(RuleDerivation.Intersection derivation, P param);

	R visit(RuleDerivation.Difference derivation, P param);

	R visit(RuleDerivation.Inverse derivation, P param);

	R visit(RuleDerivation.Transitive derivation, P param);

	R visit(RuleDerivation.SelfOrTransitive derivation, P param);

	R visit(RuleDerivation.Consecutive derivation, P param);

	R visit(RuleDerivation.CartesianProduct derivation, P param);
}
