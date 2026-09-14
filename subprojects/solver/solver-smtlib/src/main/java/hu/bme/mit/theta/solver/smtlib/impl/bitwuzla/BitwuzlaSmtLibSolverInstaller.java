/*
 *  Copyright 2026 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.common.OsHelper;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.smtlib.solver.installer.SmtLibSolverInstaller;
import hu.bme.mit.theta.solver.smtlib.solver.installer.SmtLibSolverInstallerException;
import hu.bme.mit.theta.solver.smtlib.utils.Compress;
import java.io.IOException;
import java.net.URI;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

@Deprecated
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
        // Released Bitwuzla ships a self-contained static binary, so there is nothing to compile:
        // the previous installer cloned the source and drove `configure.sh`/`make`, which stopped
        // working when upstream moved to meson and required a build toolchain on every machine.
        final var downloadUrl =
                URI.create(
                        String.format(
                                "https://github.com/bitwuzla/bitwuzla/releases/download/%s/%s",
                                version, getArchiveName()));

        logger.write(Logger.Level.MAINSTEP, "Starting download (%s)...\n", downloadUrl.toString());

        try (final var inputStream = downloadUrl.toURL().openStream()) {
            Compress.extract(inputStream, installDir, Compress.CompressionType.ZIP);
        } catch (IOException e) {
            throw new SmtLibSolverInstallerException(e);
        }

        final var binary = findBinary(installDir);
        binary.toFile().setExecutable(true, true);

        logger.write(Logger.Level.MAINSTEP, "Download finished (%s)\n", binary);
    }

    private static String getArchiveName() throws SmtLibSolverInstallerException {
        switch (OsHelper.getOs()) {
            case LINUX:
                return "Bitwuzla-Linux-x86_64-static.zip";
            case MAC:
                return "Bitwuzla-macOS-arm64-static.zip";
            case WINDOWS:
                return "Bitwuzla-Win64-x86_64-static.zip";
            default:
                throw new SmtLibSolverInstallerException(
                        "Bitwuzla is not published for " + OsHelper.getOs());
        }
    }

    /**
     * The binary, wherever the archive put it: releases nest it under a platform-named directory
     * whose exact spelling has changed between them, so it is located rather than assumed.
     */
    private static Path findBinary(final Path installDir) throws SmtLibSolverInstallerException {
        try (final var paths = Files.walk(installDir)) {
            return paths.filter(Files::isRegularFile)
                    .filter(
                            p ->
                                    p.getFileName().toString().equals("bitwuzla")
                                            || p.getFileName().toString().equals("bitwuzla.exe"))
                    .findFirst()
                    .orElseThrow(
                            () ->
                                    new SmtLibSolverInstallerException(
                                            "No bitwuzla binary in " + installDir));
        } catch (IOException e) {
            throw new SmtLibSolverInstallerException(e);
        }
    }

    @Override
    protected void uninstallSolver(final Path installDir, final String version) {
        // Default uninstall is suitable
    }

    @Override
    protected String[] getDefaultSolverArgs(String version) {
        // 0.9 rejects the old `--smt2 -i`: SMT-LIB on stdin is the default, and interpolation has
        // to be switched on for the interpolating solver to be usable at all.
        return new String[] {"--produce-interpolants"};
    }

    @Override
    public SolverFactory getSolverFactory(
            final Path installDir,
            final String version,
            final Path solverPath,
            final String[] solverArgs)
            throws SmtLibSolverInstallerException {
        final var solverFilePath = solverPath != null ? solverPath : findBinary(installDir);
        return BitwuzlaSmtLibSolverFactory.create(solverFilePath, solverArgs);
    }

    @Override
    public List<String> getSupportedVersions() {
        return List.of("0.9.1", "0.9.0", "0.8.2", "0.8.1", "0.7.0");
    }
}
