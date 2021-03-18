package hu.bme.mit.theta.solver.smtlib.impl.boolector;

import hu.bme.mit.theta.common.OsHelper;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.smtlib.impl.cvc4.CVC4SmtLibSolverFactory;
import hu.bme.mit.theta.solver.smtlib.solver.installer.SmtLibSolverInstaller;
import hu.bme.mit.theta.solver.smtlib.solver.installer.SmtLibSolverInstallerException;
import hu.bme.mit.theta.solver.smtlib.utils.Compress;
import hu.bme.mit.theta.solver.smtlib.utils.SemVer;

import java.io.BufferedReader;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.MalformedURLException;
import java.net.URI;
import java.net.URL;
import java.nio.channels.Channels;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.List;

import static hu.bme.mit.theta.common.OsHelper.Architecture.X64;
import static hu.bme.mit.theta.common.OsHelper.OperatingSystem.LINUX;
import static hu.bme.mit.theta.common.OsHelper.OperatingSystem.WINDOWS;

public class BoolectorSmtLibSolverInstaller extends SmtLibSolverInstaller.Default {

    public BoolectorSmtLibSolverInstaller(final Logger logger) {
        super(logger);
    }

    @Override
    protected String getSolverName() {
        return "boolector";
    }

    @Override
    protected void installSolver(final Path installDir, final String version) throws SmtLibSolverInstallerException {
        final var downloadUrl = URI.create(String.format(
            "https://github.com/Boolector/boolector/archive/refs/tags/%s.tar.gz",
            version
        ));

        logger.write(Logger.Level.MAINSTEP, "Starting download (%s)...\n", downloadUrl.toString());

        try(final var inputStream = downloadUrl.toURL().openStream()) {
            Compress.extract(inputStream, installDir, Compress.CompressionType.TARGZ);
        }
        catch (IOException e) {
            throw new SmtLibSolverInstallerException(e);
        }

        logger.write(Logger.Level.MAINSTEP, "Download finished\n");

        logger.write(Logger.Level.MAINSTEP, "Starting compilation\n");

        installDir.resolve("contrib").resolve("setup-lingeling.sh").toFile().setExecutable(true, true);
        executeCommand(installDir, "alias nproc=\"echo 1\" && ./contrib/setup-lingeling.sh");

        installDir.resolve("contrib").resolve("setup-btor2tools.sh").toFile().setExecutable(true, true);
        executeCommand(installDir, "alias nproc=\"echo 1\" && ./contrib/setup-btor2tools.sh");

        installDir.resolve("configure.sh").toFile().setExecutable(true, true);
        executeCommand(installDir, "./configure.sh");
        executeCommand(installDir.resolve("build"), "make");
        installDir.resolve("build").resolve("bin").resolve(getSolverBinaryName()).toFile().setExecutable(true, true);

        logger.write(Logger.Level.MAINSTEP, "Finished compilation\n");
    }

    @Override
    protected void uninstallSolver(final Path installDir, final String version) { }

    @Override
    protected String[] getDefaultSolverArgs(String version) {
        return new String[] {
            "--smt2",
            "--smt2-model",
            "-i"
        };
    }

    @Override
    public SolverFactory getSolverFactory(final Path installDir, final String version, final String[] solverArgs) throws SmtLibSolverInstallerException {
        final var solverFilePath = installDir.resolve("build").resolve("bin").resolve(getSolverBinaryName());
        return CVC4SmtLibSolverFactory.create(solverFilePath, solverArgs);
    }

    @Override
    public List<String> getSupportedVersions() {
        return Arrays.asList("3.2.1", "3.2.0", "3.1.0", "3.0.0");
    }

    private String getSolverBinaryName() {
        switch(OsHelper.getOs()) {
            case LINUX:
                return "boolector";
            default:
                throw new AssertionError();
        }
    }

    private void executeCommand(final Path workingPath, final String command) throws SmtLibSolverInstallerException {
        try {
            logger.write(Logger.Level.SUBSTEP, "Execute command: %s\n", command);
            final var process = new ProcessBuilder()
                .command("bash", "-c", command)
                .directory(workingPath.toFile())
                .redirectOutput(ProcessBuilder.Redirect.INHERIT)
                .redirectError(ProcessBuilder.Redirect.INHERIT)
                .start();

            if(process.waitFor() != 0) {
                throw new SmtLibSolverInstallerException(String.format("Error executing command: %s", command));
            }
        }
        catch (IOException | InterruptedException e) {
            throw new SmtLibSolverInstallerException(String.format("Error executing command: %s", command), e);
        }
    }
}
