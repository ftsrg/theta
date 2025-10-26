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
package hu.bme.mit.theta.solver.smtlib.impl.cvc5;

import static hu.bme.mit.theta.common.OsHelper.Architecture.X64;
import static hu.bme.mit.theta.common.OsHelper.OperatingSystem.LINUX;
import static hu.bme.mit.theta.common.OsHelper.OperatingSystem.MAC;
import static hu.bme.mit.theta.common.OsHelper.OperatingSystem.WINDOWS;

import hu.bme.mit.theta.common.OsHelper;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.smtlib.solver.SmtLibEnumStrategy;
import hu.bme.mit.theta.solver.smtlib.solver.installer.SmtLibSolverInstaller;
import hu.bme.mit.theta.solver.smtlib.solver.installer.SmtLibSolverInstallerException;
import hu.bme.mit.theta.solver.smtlib.utils.Compress;
import hu.bme.mit.theta.solver.smtlib.utils.SemVer;
import java.io.FileOutputStream;
import java.io.IOException;
import java.net.MalformedURLException;
import java.net.URI;
import java.net.URL;
import java.nio.channels.Channels;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class CVC5SmtLibSolverInstaller extends SmtLibSolverInstaller.Default {

    private static final SmtLibEnumStrategy ENUM_STRATEGY = SmtLibEnumStrategy.DATATYPES;

    private final List<SemVer.VersionDecoder> versions;

    public CVC5SmtLibSolverInstaller(final Logger logger) {
        super(logger);

        versions = new ArrayList<>();
        versions.add(
                SemVer.VersionDecoder.create(SemVer.of("1.2.0"))
                        .addString(LINUX, X64, "Linux-x86_64-static.zip")
                        .addString(MAC, X64, "macOS-x86_64-static.zip")
                        .addString(WINDOWS, X64, "Win64-x86_64-static.zip")
                        .build());
        versions.add(
                SemVer.VersionDecoder.create(SemVer.of("1.1.1"))
                        .addString(LINUX, X64, "Linux-static.zip")
                        .addString(MAC, X64, "macOS-arm64-static.zip")
                        .addString(WINDOWS, X64, "Win64-static.zip")
                        .build());
        versions.add(
                SemVer.VersionDecoder.create(SemVer.of("1.0.0"))
                        .addString(LINUX, X64, "Linux")
                        .addString(MAC, X64, "macOS")
                        .addString(WINDOWS, X64, "Win64.exe")
                        .build());
    }

    @Override
    protected String getSolverName() {
        return "cvc5";
    }

    @Override
    protected void installSolver(final Path installDir, final String version)
            throws SmtLibSolverInstallerException {
        try (final var inputStream = getDownloadUrl(version).openStream()) {
            logger.write(
                    Logger.Level.MAINSTEP,
                    "Starting download (%s)...\n",
                    getDownloadUrl(version).toString());
            if (SemVer.of(version).compareTo(SemVer.of("1.1.1")) < 0) {
                try (final var inputChannel = Channels.newChannel(inputStream);
                        final var outputChannel =
                                new FileOutputStream(
                                                installDir
                                                        .resolve(getSolverBinaryName(version))
                                                        .toAbsolutePath()
                                                        .toString())
                                        .getChannel()) {
                    outputChannel.transferFrom(inputChannel, 0, Long.MAX_VALUE);
                    installDir
                            .resolve(getSolverBinaryName(version))
                            .toFile()
                            .setExecutable(true, true);
                }
            } else {
                Compress.extract(inputStream, installDir, Compress.CompressionType.ZIP);
                installDir
                        .resolve("bin")
                        .resolve(getSolverBinaryName(version))
                        .toFile()
                        .setExecutable(true, true);
            }

        } catch (IOException e) {
            throw new SmtLibSolverInstallerException(e);
        }
        try (final var inputChannel = Channels.newChannel(getLicenseDownloadUrl().openStream());
                final var outputChannel =
                        new FileOutputStream(
                                        installDir.resolve("COPYING").toAbsolutePath().toString())
                                .getChannel()) {
            logger.write(
                    Logger.Level.MAINSTEP,
                    "Starting license download (%s)...\n",
                    getLicenseDownloadUrl().toString());
            outputChannel.transferFrom(inputChannel, 0, Long.MAX_VALUE);
        } catch (IOException e) {
            throw new SmtLibSolverInstallerException(e);
        }

        logger.write(Logger.Level.MAINSTEP, "Download finished\n");
    }

    @Override
    protected void uninstallSolver(final Path installDir, final String version) {
        // Default uninstall is suitable
    }

    @Override
    protected String[] getDefaultSolverArgs(String version) {
        return new String[] {
            "--lang", "smt2", "--output-lang", "smt2", "--quiet", "--incremental", "--fp-exp"
        };
    }

    @Override
    public SolverFactory getSolverFactory(
            final Path installDir,
            final String version,
            final Path solverPath,
            final String[] solverArgs)
            throws SmtLibSolverInstallerException {
        final Path solverFilePath;
        if (SemVer.of(version).compareTo(SemVer.of("1.1.1")) < 0) {
            solverFilePath =
                    solverPath != null
                            ? solverPath
                            : installDir.resolve(getSolverBinaryName(version));
        } else {
            solverFilePath =
                    solverPath != null
                            ? solverPath
                            : installDir.resolve("bin").resolve(getSolverBinaryName(version));
        }
        return CVC5SmtLibSolverFactory.create(solverFilePath, solverArgs, ENUM_STRATEGY);
    }

    @Override
    public List<String> getSupportedVersions() {
        return Arrays.asList(
                "1.3.1", "1.3.0", "1.2.1", "1.2.0",
                "1.1.2", "1.1.1", "1.1.0", "1.0.9", "1.0.8", "1.0.7", "1.0.6", "1.0.5", "1.0.4",
                "1.0.3", "1.0.2", "1.0.1", "1.0.0");
    }

    private URL getDownloadUrl(final String version)
            throws SmtLibSolverInstallerException, MalformedURLException {
        return URI.create(
                        String.format(
                                "https://github.com/cvc5/cvc5/releases/download/cvc5-%s/cvc5-%s",
                                version, getArchString(version)))
                .toURL();
    }

    private URL getLicenseDownloadUrl()
            throws SmtLibSolverInstallerException, MalformedURLException {
        return URI.create("https://raw.githubusercontent.com/cvc5/cvc5/main/COPYING").toURL();
    }

    private String getArchString(final String version) throws SmtLibSolverInstallerException {
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
                            "CVC5 on operating system %s and architecture %s is not supported",
                            OsHelper.getOs(), OsHelper.getArch()));
        }

        return archStr;
    }

    private String getSolverBinaryName(final String version) throws SmtLibSolverInstallerException {
        if (SemVer.of(version).compareTo(SemVer.of("1.1.1")) < 0) {
            return String.format("cvc5-%s", getArchString(version));
        } else {
            return OsHelper.getOs() == WINDOWS ? "cvc5.exe" : "cvc5";
        }
    }
}
