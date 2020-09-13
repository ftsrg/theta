package hu.bme.mit.theta.solver.smtlib;

import hu.bme.mit.theta.common.logging.Logger;

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

public abstract class BaseSmtLibSolverInstaller implements SmtLibSolverInstaller {
    protected final Logger logger;

    public BaseSmtLibSolverInstaller(final Logger logger) {
        this.logger = logger;
    }

    @Override
    public final void install(Path home, String version, String name) throws SmtLibSolverInstallerException {
        checkNotNull(home);
        checkArgument(Files.exists(home));
        checkVersion(version);
        checkName(name);

        final var installDir = getInstallDir(home, name);
        if(Files.exists(installDir)) {
            throw new SmtLibSolverInstallerException("There is already a solver instance with this name installed");
        }

        try {
            logger.write(Logger.Level.MAINSTEP, "Beginning installation...\n");

            Files.createDirectory(installDir);

            installSolver(installDir, version);

            final var solverArgsPath = argsFile(installDir);
            Files.writeString(solverArgsPath, String.join("\n", getDefaultSolverArgs(version)), StandardCharsets.UTF_8);

            final var solverInfoPath = infoFile(installDir);
            Files.writeString(
                solverInfoPath,
                String.format("solver=%s\n", getSolverName()) +
                String.format("version=%s\n", version) +
                String.format("name=%s\n", name),
                StandardCharsets.UTF_8
            );

            logger.write(Logger.Level.MAINSTEP, "Installation finished\n");
        }
        catch (SmtLibSolverInstallerException e) {
            uninstall(home, version);
            throw e;
        }
        catch (IOException e) {
            throw new SmtLibSolverInstallerException(String.format("Error: %s", e.getMessage()), e);
        }
    }

    @Override
    public final void uninstall(Path home, String version) throws SmtLibSolverInstallerException {
        checkNotNull(home);
        checkArgument(Files.exists(home));
        checkName(version);

        final var installDir = getInstallDir(home, version);
        if(!Files.exists(installDir)) {
            throw new SmtLibSolverInstallerException("The version is not installed");
        }

        try {
            logger.write(Logger.Level.MAINSTEP, "Beginning uninstallation...\n");

            uninstallSolver(installDir, version);

            deleteDirectory(installDir.toFile());

            logger.write(Logger.Level.MAINSTEP, "Uninstallation finished\n");
        }
        catch (IOException e) {
            throw new SmtLibSolverInstallerException(String.format("Error: %s", e.getMessage()), e);
        }
    }

    @Override
    public void reinstall(Path home, String version) throws SmtLibSolverInstallerException {
        checkNotNull(home);
        checkArgument(Files.exists(home));
        checkName(version);

        final String solverVersion;
        try {
            final var installDir = getInstallDir(home, version);
            final var solverInfoPath = infoFile(installDir);
            final var solverInfo = Files
                .readAllLines(solverInfoPath, StandardCharsets.UTF_8).stream()
                .filter(l -> l.startsWith("version="))
                .map(l -> l.substring("version=".length()))
                .findAny();

            if(solverInfo.isPresent()) {
                solverVersion = solverInfo.get();
            }
            else {
                throw new SmtLibSolverInstallerException("The solver installation is corrupted");
            }
        }
        catch (IOException e) {
            throw new SmtLibSolverInstallerException(String.format("Error: %s", e.getMessage()), e);
        }

        uninstall(home, version);
        install(home, solverVersion, version);
    }

    @Override
    public final String getInfo(Path home, String version) throws SmtLibSolverInstallerException {
        checkNotNull(home);
        checkArgument(Files.exists(home));
        checkName(version);

        final var installDir = getInstallDir(home, version);
        if(!Files.exists(installDir)) {
            throw new SmtLibSolverInstallerException("The version is not installed");
        }

        try {
            final var solverInfoPath = infoFile(installDir);
            final var solverInfoStr = Files.readString(solverInfoPath, StandardCharsets.UTF_8);
            final var solverArgsPath = argsFile(installDir);
            final var solverArgs = Files.readAllLines(solverArgsPath, StandardCharsets.UTF_8).toArray(String[]::new);

            return solverInfoStr + String.format("args=%s\n", String.join(" ", solverArgs));
        }
        catch (IOException e) {
            throw new SmtLibSolverInstallerException(String.format("Error: %s", e.getMessage()), e);
        }
    }

    @Override
    public final Path getArgsFile(Path home, String version) throws SmtLibSolverInstallerException {
        checkNotNull(home);
        checkArgument(Files.exists(home));
        checkName(version);

        final var installDir = home.resolve(version);
        if(!Files.exists(installDir)) {
            throw new SmtLibSolverInstallerException("The version is not installed");
        }

        return argsFile(installDir);
    }

    @Override
    public final List<String> getInstalledVersions(Path home) throws SmtLibSolverInstallerException {
        checkNotNull(home);

        if(Files.exists(home)) {
            final var installedDirs = home.toFile()
                .list((current, name) -> new File(current, name).isDirectory());

            assert installedDirs != null;
            return Arrays.asList(installedDirs);
        }
        else {
            return Collections.emptyList();
        }
    }

    protected abstract String getSolverName() throws SmtLibSolverInstallerException;
    protected abstract void installSolver(final Path installDir, final String version) throws SmtLibSolverInstallerException;
    protected abstract void uninstallSolver(final Path installDir, final String version) throws SmtLibSolverInstallerException;
    protected abstract String[] getDefaultSolverArgs(final String version) throws SmtLibSolverInstallerException;

    protected final void checkName(final String version) throws SmtLibSolverInstallerException {
        if(!version.matches("^[a-zA-Z0-9_.-]+$")) {
            throw new SmtLibSolverInstallerException("Unsupported name format: " + version);
        }
    }

    protected final void checkVersion(final String version) throws SmtLibSolverInstallerException {
        if(!version.matches("^[0-9]+(\\.[0-9]+)*$")) {
            throw new SmtLibSolverInstallerException("Unsupported version format: " + version);
        }
    }

    protected final Path getInstallDir(final Path home, final String version) {
        return home.resolve(version);
    }

    protected final Path argsFile(final Path installDir) {
        return installDir.resolve("solver-args.txt");
    }

    protected final Path infoFile(final Path installDir) {
        return installDir.resolve("solver-info.txt");
    }

    private void deleteDirectory(File directoryToBeDeleted) throws IOException {
        File[] allContents = directoryToBeDeleted.listFiles();
        if (allContents != null) {
            for (File file : allContents) {
                deleteDirectory(file);
            }
        }

        Files.delete(directoryToBeDeleted.toPath());
    }
}
