package hu.bme.mit.theta.solver.smtlib.generic;

import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.smtlib.SmtLibSolverInstaller;
import hu.bme.mit.theta.solver.smtlib.SmtLibSolverInstallerException;
import hu.bme.mit.theta.solver.smtlib.manager.SmtLibSolverManager;

import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

public final class GenericSmtLibSolverInstaller implements SmtLibSolverInstaller {
    final Logger logger;

    public GenericSmtLibSolverInstaller(Logger logger) {
        this.logger = logger;
    }

    @Override
    public void install(final Path home, final String version) throws SmtLibSolverInstallerException {
        checkNotNull(home);
        checkArgument(Files.exists(home));
        checkVersion(version);
        throw new SmtLibSolverInstallerException("Unsupported operation for generic solvers");
    }

    public void install(final Path home, final String version, final Path solverPath, final String[] solverArgs) throws SmtLibSolverInstallerException {
        checkNotNull(home);
        checkArgument(Files.exists(home));
        checkVersion(version);
        checkArgument(Files.exists(solverPath));
        checkNotNull(solverArgs);

        final var installDir = home.resolve(version);
        if(Files.exists(installDir)) {
            throw new SmtLibSolverInstallerException("The version is already installed");
        }

        try {
            logger.write(Logger.Level.MAINSTEP, "Beginning installation...\n");

            Files.createDirectory(installDir);

            final var solverFilePath = solverFile(installDir);
            Files.writeString(solverFilePath, solverPath.toAbsolutePath().toString(), StandardCharsets.UTF_8);

            final var solverArgsPath = argsFile(installDir);
            Files.writeString(solverArgsPath, String.join("\n", solverArgs), StandardCharsets.UTF_8);

            logger.write(Logger.Level.MAINSTEP, "Installation finished");
        }
        catch (IOException e) {
            throw new SmtLibSolverInstallerException(String.format("Error: %s", e.getMessage()), e);
        }
    }

    @Override
    public void uninstall(final Path home, final String version) throws SmtLibSolverInstallerException {
        checkNotNull(home);
        checkArgument(Files.exists(home));
        checkVersion(version);

        final var installDir = home.resolve(version);
        if(!Files.exists(installDir)) {
            throw new SmtLibSolverInstallerException("The version is not installed");
        }

        try {
            logger.write(Logger.Level.MAINSTEP, "Beginning uninstallation...\n");

            final var solverFilePath = solverFile(installDir);
            Files.delete(solverFilePath);
            final var solverArgsPath = argsFile(installDir);
            Files.delete(solverArgsPath);

            Files.delete(installDir);

            logger.write(Logger.Level.MAINSTEP, "Uninstallation finished");
        }
        catch (IOException e) {
            throw new SmtLibSolverInstallerException(String.format("Error: %s", e.getMessage()), e);
        }

    }

    @Override
    public void reinstall(final Path home, final String version) throws SmtLibSolverInstallerException {
        checkNotNull(home);
        checkArgument(Files.exists(home));
        checkVersion(version);
        throw new SmtLibSolverInstallerException("Unsupported operation for generic solvers");
    }

    @Override
    public String getInfo(final Path home, final String version) throws SmtLibSolverInstallerException {
        checkNotNull(home);
        checkArgument(Files.exists(home));
        checkVersion(version);

        final var installDir = home.resolve(version);
        if(!Files.exists(installDir)) {
            throw new SmtLibSolverInstallerException("The version is not installed");
        }

        try {
            final var solverFilePath = solverFile(installDir);
            final var solverPathStr = Files.readAllLines(solverFilePath, StandardCharsets.UTF_8).get(0);
            final var solverArgsPath = argsFile(installDir);
            final var solverArgs = Files.readAllLines(solverArgsPath, StandardCharsets.UTF_8).toArray(String[]::new);

            return "Generic solver" +
                   "Solver binary: " + solverPathStr +
                   "Arguments: " + String.join(" ", solverArgs);
        }
        catch (IOException e) {
            throw new SmtLibSolverInstallerException(String.format("Error: %s", e.getMessage()), e);
        }
    }

    @Override
    public Path getArgsFile(final Path home, final String version) throws SmtLibSolverInstallerException {
        checkNotNull(home);
        checkArgument(Files.exists(home));
        checkVersion(version);

        final var installDir = home.resolve(version);
        if(!Files.exists(installDir)) {
            throw new SmtLibSolverInstallerException("The version is not installed");
        }

        return argsFile(installDir);
    }

    @Override
    public SolverFactory getSolverFactory(final Path home, final String version) throws SmtLibSolverInstallerException {
        checkNotNull(home);
        checkArgument(Files.exists(home));
        checkVersion(version);

        final var installDir = home.resolve(version);
        if(!Files.exists(installDir)) {
            throw new SmtLibSolverInstallerException("The version is not installed");
        }

        try {
            final var solverFilePath = solverFile(installDir);
            final var solverPathStr = Files.readAllLines(solverFilePath, StandardCharsets.UTF_8).get(0);
            final var solverArgsPath = argsFile(installDir);
            final var solverArgs = Files.readAllLines(solverArgsPath, StandardCharsets.UTF_8).toArray(String[]::new);

            return GenericSmtLibSolverFactory.create(Path.of(solverPathStr), solverArgs);
        }
        catch (IOException e) {
            throw new SmtLibSolverInstallerException(String.format("Error: %s", e.getMessage()), e);
        }
    }

    @Override
    public List<String> getSupportedVersions() throws SmtLibSolverInstallerException {
        return Collections.emptyList();
    }

    @Override
    public List<String> getInstalledVersions(final Path home) throws SmtLibSolverInstallerException {
        checkNotNull(home);
        checkArgument(Files.exists(home));

        final var installedDirs = home.toFile()
            .list((current, name) -> new File(current, name).isDirectory());

        assert installedDirs != null;
        return Arrays.asList(installedDirs);
    }

    private void checkVersion(final String version) throws SmtLibSolverInstallerException {
        if(!version.matches("^[a-zA-Z0-9_.-]+$")) {
            throw new SmtLibSolverInstallerException("Unsupported version format: " + version);
        }
    }

    private Path solverFile(final Path installDir) {
        return installDir.resolve("solver.txt");
    }

    private Path argsFile(final Path installDir) {
        return installDir.resolve("solver-args.txt");
    }
}
