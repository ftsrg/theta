/*
 *  Copyright 2023 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.solver.smtlib.impl.bitwuzla;

import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.smtlib.solver.installer.SmtLibSolverInstaller;
import hu.bme.mit.theta.solver.smtlib.solver.installer.SmtLibSolverInstallerException;
import hu.bme.mit.theta.solver.smtlib.utils.Compress;

import java.io.IOException;
import java.net.URI;
import java.nio.file.Path;
import java.util.List;

public class BitwuzlaSmtLibSolverInstaller extends SmtLibSolverInstaller.Default {

    public BitwuzlaSmtLibSolverInstaller(final Logger logger) {
        super(logger);
    }

    @Override
    protected String getSolverName() {
        return "bitwuzla";
    }

    @Override
    protected void installSolver(final Path installDir, final String version)
            throws SmtLibSolverInstallerException {
        final var downloadUrl = URI.create(String.format(
                "https://github.com/bitwuzla/bitwuzla/archive/%s.zip",
                version
        ));

        logger.write(Logger.Level.MAINSTEP, "Starting download (%s)...\n", downloadUrl.toString());

        try (final var inputStream = downloadUrl.toURL().openStream()) {
            Compress.extract(inputStream, installDir, Compress.CompressionType.ZIP);
        } catch (IOException e) {
            throw new SmtLibSolverInstallerException(e);
        }

        logger.write(Logger.Level.MAINSTEP, "Download finished\n");

        logger.write(Logger.Level.MAINSTEP, "Starting compilation\n");

        installDir.resolve("contrib").resolve("setup-cadical.sh").toFile()
                .setExecutable(true, true);
        executeCommand(installDir, "./contrib/setup-cadical.sh");

        installDir.resolve("contrib").resolve("setup-btor2tools.sh").toFile()
                .setExecutable(true, true);
        executeCommand(installDir, "./contrib/setup-btor2tools.sh");

        installDir.resolve("contrib").resolve("setup-symfpu.sh").toFile().setExecutable(true, true);
        executeCommand(installDir, "./contrib/setup-symfpu.sh");

        installDir.resolve("configure.sh").toFile().setExecutable(true, true);
        executeCommand(installDir, "./configure.sh");
        executeCommand(installDir.resolve("build"), "make");
        installDir.resolve("build").resolve("bin").resolve("bitwuzla").toFile()
                .setExecutable(true, true);

        logger.write(Logger.Level.MAINSTEP, "Finished compilation\n");
    }

    @Override
    protected void uninstallSolver(final Path installDir, final String version) {
        // Default uninstall is suitable
    }

    @Override
    protected String[] getDefaultSolverArgs(String version) {
        return new String[]{
                "--smt2",
                "-i"
        };
    }

    @Override
    public SolverFactory getSolverFactory(final Path installDir, final String version,
                                          final Path solverPath, final String[] solverArgs) throws SmtLibSolverInstallerException {
        final var solverFilePath = solverPath != null ? solverPath
                : installDir.resolve("build").resolve("bin").resolve("bitwuzla");
        return BitwuzlaSmtLibSolverFactory.create(solverFilePath, solverArgs);
    }

    @Override
    public List<String> getSupportedVersions() {
        return List.of("3ea759df11285e722b565c0b5c132dc0bb77066f");
    }

    private void executeCommand(final Path workingPath, final String command)
            throws SmtLibSolverInstallerException {
        try {
            logger.write(Logger.Level.SUBSTEP, "Execute command: %s\n", command);
            final var process = new ProcessBuilder()
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
