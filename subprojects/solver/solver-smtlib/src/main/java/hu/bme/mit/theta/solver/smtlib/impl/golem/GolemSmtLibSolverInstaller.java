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
package hu.bme.mit.theta.solver.smtlib.impl.golem;

import static hu.bme.mit.theta.common.OsHelper.Architecture.X64;
import static hu.bme.mit.theta.common.OsHelper.OperatingSystem.LINUX;

import hu.bme.mit.theta.common.OsHelper;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.smtlib.solver.installer.SmtLibSolverInstaller;
import hu.bme.mit.theta.solver.smtlib.solver.installer.SmtLibSolverInstallerException;
import hu.bme.mit.theta.solver.smtlib.utils.Compress;
import hu.bme.mit.theta.solver.smtlib.utils.Compress.CompressionType;
import hu.bme.mit.theta.solver.smtlib.utils.SemVer;
import java.net.URI;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class GolemSmtLibSolverInstaller extends SmtLibSolverInstaller.Default {

    private final List<SemVer.VersionDecoder> versions;

    public GolemSmtLibSolverInstaller(final Logger logger) {
        super(logger);

        versions = new ArrayList<>();
        versions.add(
                SemVer.VersionDecoder.create(SemVer.of("0.8.1"))
                        .addString(LINUX, X64, "x64-linux.tar.bz2")
                        .build());
        versions.add(
                SemVer.VersionDecoder.create(SemVer.of("0.5.0"))
                        .addString(LINUX, X64, "0.5.0-x64-linux.tar.bz2")
                        .build());
    }

    @Override
    protected String getSolverName() {
        return "golem";
    }

    @Override
    protected void installSolver(final Path installDir, final String version)
            throws SmtLibSolverInstallerException {
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
                                "https://github.com/usi-verification-and-security/golem/releases/download/v%s/golem-%s",
                                version, archStr));

        logger.write(Logger.Level.MAINSTEP, "Starting download (%s)...\n", downloadUrl.toString());
        try (final var inputStream = downloadUrl.toURL().openStream()) {
            Compress.extractTarbomb(inputStream, installDir, CompressionType.TARBZ2);
            installDir.resolve(getSolverBinaryName()).toFile().setExecutable(true, true);
        } catch (Exception e) {
            throw new SmtLibSolverInstallerException(e);
        }

        logger.write(Logger.Level.MAINSTEP, "Download finished\n");
    }

    @Override
    protected void uninstallSolver(Path installDir, String version) {
        // Default uninstall is suitable
    }

    @Override
    protected String[] getDefaultSolverArgs(String version) {
        if (SemVer.of(version).compareTo(SemVer.of("0.8.1")) >= 0) {
            return new String[] {"--print-witness" /*, "-portfolio"*/};
        }
        return new String[] {"--print-witness"};
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
        return GolemSmtLibSolverFactory.create(solverFilePath, solverArgs, version.equals("0.5.0"));
    }

    @Override
    public List<String> getSupportedVersions() {
        return Arrays.asList("0.5.0", "0.8.1", "0.9.0");
    }

    private String getSolverBinaryName() {
        switch (OsHelper.getOs()) {
            case LINUX:
                return "golem";
            default:
                throw new AssertionError();
        }
    }
}
