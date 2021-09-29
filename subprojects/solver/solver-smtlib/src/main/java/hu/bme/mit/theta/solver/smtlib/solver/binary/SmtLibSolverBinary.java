package hu.bme.mit.theta.solver.smtlib.solver.binary;

public interface SmtLibSolverBinary extends AutoCloseable {
    void issueCommand(String command);
    String readResponse();
}
