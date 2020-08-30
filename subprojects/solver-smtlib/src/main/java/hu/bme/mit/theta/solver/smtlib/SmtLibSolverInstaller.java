package hu.bme.mit.theta.solver.smtlib;

import hu.bme.mit.theta.solver.SolverFactory;

import java.nio.file.Path;
import java.util.List;

public interface SmtLibSolverInstaller {
    void install(Path home, String version) throws SmtLibSolverInstallerException;

    void uninstall(Path home, String version) throws SmtLibSolverInstallerException;

    void reinstall(Path home, String version) throws SmtLibSolverInstallerException;

    String getInfo(Path home, String version) throws SmtLibSolverInstallerException;

    Path getArgsFile(Path home, String version) throws SmtLibSolverInstallerException;

    SolverFactory getSolverFactory(Path home, String version) throws SmtLibSolverInstallerException;

    List<String> getSupportedVersions() throws SmtLibSolverInstallerException;

    List<String> getInstalledVersions(Path home) throws SmtLibSolverInstallerException;
}
