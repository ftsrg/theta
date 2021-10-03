package hu.bme.mit.theta.cat.solver;

public interface ProgramBuilder<ProgramLoc, Variable, Thread> {
	void addReadProgramLoc(final ProgramLoc programLoc, final Thread thread, final Variable variable);
	void addWriteProgramLoc(final ProgramLoc programLoc, final Thread thread, final Variable variable);
	void addFenceLoc(final ProgramLoc programLoc, final Thread thread);
	void addProgramLoc(final ProgramLoc programLoc);
	void addProgramLoc(final ProgramLoc programLoc, final Thread thread);
	void addProgramLoc(final ProgramLoc programLoc, final Thread thread, final Variable variable);
	void addPoEdge(final ProgramLoc programLocA, final ProgramLoc programLocB);
	MemoryModelSolver<ProgramLoc, ProgramLoc> build();
}
