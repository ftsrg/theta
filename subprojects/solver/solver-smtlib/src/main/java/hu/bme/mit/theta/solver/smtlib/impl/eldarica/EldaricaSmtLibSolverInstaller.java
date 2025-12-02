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
package hu.bme.mit.theta.solver.smtlib.impl.eldarica;

import static hu.bme.mit.theta.common.OsHelper.Architecture.X64;
import static hu.bme.mit.theta.common.OsHelper.OperatingSystem.LINUX;

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
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class EldaricaSmtLibSolverInstaller extends SmtLibSolverInstaller.Default {

    private final List<SemVer.VersionDecoder> versions;

    private final YicesSmtLibSolverInstaller yicesInstaller =
            new YicesSmtLibSolverInstaller(logger);
    private static final String YICES_VERSION = "1.0.40";

    public EldaricaSmtLibSolverInstaller(final Logger logger) {
        super(logger);

        versions = new ArrayList<>();
        versions.add(
                SemVer.VersionDecoder.create(SemVer.of("2.2"))
                        .addString(LINUX, X64, "zip")
                        .build());
        versions.add(
                SemVer.VersionDecoder.create(SemVer.of("2.1"))
                        .addString(LINUX, X64, "zip")
                        .build());
    }

    @Override
    protected String getSolverName() {
        return "eldarica";
    }

    @Override
    protected void installSolver(final Path installDir, final String version)
            throws SmtLibSolverInstallerException {
        final var yicesPath = getInstallDir(installDir, "yices");
        yicesInstaller.installSolver(yicesPath, "1.0.40"); // dependency

        final var semVer = SemVer.of(version);
        String archStr = null;

        for (final var versionDecoder : versions) {
            if (semVer.compareTo(versionDecoder.getVersion()) >= 0) {
                archStr = versionDecoder.getOsArchString(OsHelper.getOs(), OsHelper.getArch());
                break;
            }
        }
        if (archStr == null) {
            throw new SmtLibSolverInstallerException(
                    String.format(
                            "%s on operating system %s and architecture %s is not supported",
                            getSolverName(), OsHelper.getOs(), OsHelper.getArch()));
        }

        final var downloadUrl =
                URI.create(
                        String.format(
                                "https://github.com/uuverifiers/eldarica/releases/download/v%s/eldarica-bin-%s.%s",
                                version, version, archStr));

        logger.write(Logger.Level.MAINSTEP, "Starting download (%s)...\n", downloadUrl.toString());
        try (final var inputStream = downloadUrl.toURL().openStream()) {
            Compress.extract(inputStream, installDir, Compress.CompressionType.ZIP);
            installDir.resolve(getSolverBinaryName()).toFile().setExecutable(true, true);
        } catch (IOException e) {
            throw new SmtLibSolverInstallerException(e);
        }

        logger.write(Logger.Level.MAINSTEP, "Download finished\n");
    }

    @Override
    protected void uninstallSolver(Path installDir, String version) {
        final var yicesPath = getInstallDir(installDir, "yices");
        yicesInstaller.uninstallSolver(yicesPath, YICES_VERSION);
        // Default uninstall is suitable
    }

    @Override
    protected String[] getDefaultSolverArgs(String version) {
        return new String[] {"-ssol", "-scex", "-portfolio"};
    }

    @Override
    public SolverFactory getSolverFactory(
            final Path installDir,
            final String version,
            final Path solverPath,
            final String[] solverArgs)
            throws SmtLibSolverInstallerException {
        final var solverFilePath =
                solverPath != null ? solverPath : installDir.resolve(getSolverBinaryName());
        final var yicesPath = installDir.resolve("yices").resolve("bin");
        return EldaricaSmtLibSolverFactory.create(
                solverFilePath, solverArgs, yicesPath, version.equals("2.1"));
    }

    @Override
    public List<String> getSupportedVersions() {
        return Arrays.asList("2.1", "2.2");
    }

    private String getSolverBinaryName() {
        switch (OsHelper.getOs()) {
            case LINUX:
                return "eld";
            default:
                throw new AssertionError();
        }
    }
}
