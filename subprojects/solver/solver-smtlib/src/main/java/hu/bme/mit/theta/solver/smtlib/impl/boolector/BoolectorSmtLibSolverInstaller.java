/*
 *  Copyright 2025 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.solver.smtlib.impl.boolector;

import hu.bme.mit.theta.common.OsHelper;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.smtlib.solver.installer.SmtLibSolverInstaller;
import hu.bme.mit.theta.solver.smtlib.solver.installer.SmtLibSolverInstallerException;
import hu.bme.mit.theta.solver.smtlib.utils.Compress;
import hu.bme.mit.theta.solver.smtlib.utils.SemVer;
import java.io.IOException;
import java.net.URI;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.List;

public class BoolectorSmtLibSolverInstaller extends SmtLibSolverInstaller.Default {

    public BoolectorSmtLibSolverInstaller(final Logger logger) {
        super(logger);
    }

    @Override
    protected String getSolverName() {
        return "boolector";
    }

    @Override
    protected void installSolver(final Path installDir, final String version)
            throws SmtLibSolverInstallerException {
        final var downloadUrl =
                URI.create(
                        String.format(
                                "https://github.com/Boolector/boolector/archive/refs/tags/%s.tar.gz",
                                version));

        logger.write(Logger.Level.MAINSTEP, "Starting download (%s)...\n", downloadUrl.toString());

        try (final var inputStream = downloadUrl.toURL().openStream()) {
            Compress.extract(inputStream, installDir, Compress.CompressionType.TARGZ);
        } catch (IOException e) {
            throw new SmtLibSolverInstallerException(e);
        }

        logger.write(Logger.Level.MAINSTEP, "Download finished\n");

        logger.write(Logger.Level.MAINSTEP, "Starting compilation\n");

        installDir
                .resolve("contrib")
                .resolve("setup-lingeling.sh")
                .toFile()
                .setExecutable(true, true);
        executeCommand(installDir, "alias nproc=\"echo 1\" && ./contrib/setup-lingeling.sh");

        installDir
                .resolve("contrib")
                .resolve("setup-btor2tools.sh")
                .toFile()
                .setExecutable(true, true);
        executeCommand(installDir, "alias nproc=\"echo 1\" && ./contrib/setup-btor2tools.sh");

        installDir.resolve("configure.sh").toFile().setExecutable(true, true);
        executeCommand(installDir, "./configure.sh");
        executeCommand(installDir.resolve("build"), "make");
        installDir
                .resolve("build")
                .resolve("bin")
                .resolve(getSolverBinaryName())
                .toFile()
                .setExecutable(true, true);

        logger.write(Logger.Level.MAINSTEP, "Finished compilation\n");
    }

    @Override
    protected void uninstallSolver(final Path installDir, final String version) {
        // Default uninstall is suitable
    }

    @Override
    protected String[] getDefaultSolverArgs(String version) {
        if (SemVer.of(version).compareTo(SemVer.of("3.2.2")) >= 0) {
            return new String[] {"--smt2", "-i"};
        } else {
            return new String[] {"--smt2", "--smt2-model", "-i"};
        }
    }

    @Override
    public SolverFactory getSolverFactory(
            final Path installDir,
            final String version,
            final Path solverPath,
            final String[] solverArgs)
            throws SmtLibSolverInstallerException {
        final var solverFilePath =
                solverPath != null
                        ? solverPath
                        : installDir.resolve("build").resolve("bin").resolve(getSolverBinaryName());
        return BoolectorSmtLibSolverFactory.create(solverFilePath, solverArgs);
    }

    @Override
    public List<String> getSupportedVersions() {
        return Arrays.asList("3.2.2", "3.2.1", "3.2.0", "3.1.0", "3.0.0");
    }

    private String getSolverBinaryName() {
        switch (OsHelper.getOs()) {
            case LINUX:
                return "boolector";
            default:
                throw new AssertionError();
        }
    }

    private void executeCommand(final Path workingPath, final String command)
            throws SmtLibSolverInstallerException {
        try {
            logger.write(Logger.Level.SUBSTEP, "Execute command: %s\n", command);
            final var process =
                    new ProcessBuilder()
                            .command("bash", "-c", command)
                            .directory(workingPath.toFile())
                            .redirectOutput(ProcessBuilder.Redirect.INHERIT)
                            .redirectError(ProcessBuilder.Redirect.INHERIT)
                            .start();

            if (process.waitFor() != 0) {
                throw new SmtLibSolverInstallerException(
                        String.format("Error executing command: %s", command));
            }
        } catch (IOException | InterruptedException e) {
            throw new SmtLibSolverInstallerException(
                    String.format("Error executing command: %s", command), e);
        }
    }
}
