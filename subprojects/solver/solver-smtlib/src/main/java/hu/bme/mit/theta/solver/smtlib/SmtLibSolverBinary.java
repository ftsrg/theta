package hu.bme.mit.theta.solver.smtlib;

public interface SmtLibSolverBinary {
    void issueCommand(String command);
    String readResponse();
}
