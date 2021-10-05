package hu.bme.mit.theta.cat.solver;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;

import java.util.List;

public interface ProgramBuilder<ProgramLoc, Variable, Thread> {
	void addReadProgramLoc(final ProgramLoc programLoc, final Thread thread, final Variable variable);
	void addWriteProgramLoc(final ProgramLoc programLoc, final Thread thread, final Variable variable);
	void addFenceLoc(final ProgramLoc programLoc, final Thread thread);
	void addProgramLoc(final ProgramLoc programLoc);
	void addProgramLoc(final ProgramLoc programLoc, final Thread thread);
	void addProgramLoc(final ProgramLoc programLoc, final Thread thread, final Variable variable);
	void addPoEdge(final ProgramLoc programLocA, final ProgramLoc programLocB);

	String createProduct(final String newRule, final String existingRule1, final String existingRule2);
	String createAlternative(final String newRule, final String existingRule);
	String createUnion(final String newRule, final String existingRule1, final String existingRule2);
	String createIntersection(final String newRule, final String existingRule1, final String existingRule2);
	String createDifference(final String newRule, final String existingRule1, final String existingRule2);
	String createInverse(final String newRule, final String existingRule);
	String createTransitive(final String newRule, final String existingRule);
	String createSelfTransitive(final String newRule, final String existingRule);
	String createSuccessor(final String newRule, final String existingRule1, final String existingRule2);
	String createRelation(final String newRelation, final int arity);

	void assertIrreflexive(final String rule);
	void assertEmpty(final String rule);
	void assertAcyclic(final String rule);

	MemoryModelSolver<ProgramLoc, ProgramLoc> build(List<Tuple2<XcfaLabel, ConstDecl<?>>> dataFlow);

	void pop();
	void push();
}
