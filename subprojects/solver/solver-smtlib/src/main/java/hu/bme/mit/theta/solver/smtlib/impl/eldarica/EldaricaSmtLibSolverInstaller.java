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
import java.io.InputStreamReader;
import java.io.BufferedReader;
import java.net.URI;
import java.nio.charset.StandardCharsets;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class EldaricaSmtLibSolverInstaller extends SmtLibSolverInstaller.Default {

    private final List<SemVer.VersionDecoder> versions;

    private final YicesSmtLibSolverInstaller yicesInstaller = new YicesSmtLibSolverInstaller();
    private static final String YICES_VERSION = "1.0.40";

    public EldaricaSmtLibSolverInstaller() {

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
            yicesInstaller.installSolver(yicesPath, YICES_VERSION);

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

        Logger.mainStep("Starting download (%s)...\n", downloadUrl.toString());
        try (final var inputStream = downloadUrl.toURL().openStream()) {
            Compress.extract(inputStream, installDir, Compress.CompressionType.ZIP);
            installDir.resolve(getSolverBinaryName()).toFile().setExecutable(true, true);
        } catch (IOException e) {
            throw new SmtLibSolverInstallerException(e);
        }

        Logger.mainStep("Download finished\n");
    }


    @Override
    protected void uninstallSolver(Path installDir, String version) {
        final var yicesPath = getInstallDir(installDir, "yices");
        yicesInstaller.uninstallSolver(yicesPath, YICES_VERSION);
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
        final var yicesInstallPath = getInstallDir(installDir, "yices");
        final var yicesPath = yicesInstallPath.resolve("bin");
        final var yicesBinary = yicesPath.resolve("yices");
        if (!yicesBinary.toFile().canExecute() || !isUsableYices(yicesBinary)) {
            Logger.mainStep("Yices binary not found in %s, installing it now...%n", yicesPath);
            yicesInstaller.installSolver(yicesInstallPath, YICES_VERSION);
        }
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

    private boolean isUsableYices(final Path yicesBinary) {
        try {
            final var process =
                    new ProcessBuilder(yicesBinary.toAbsolutePath().toString(), "--version").start();
            final var output = new StringBuilder();
            try (final var reader =
                    new BufferedReader(
                            new InputStreamReader(process.getInputStream(), StandardCharsets.UTF_8))) {
                String line;
                while ((line = reader.readLine()) != null) {
                    if (!output.isEmpty()) {
                        output.append(' ');
                    }
                    output.append(line);
                }
            }
            process.waitFor();
            final var versionOutput = output.toString();
            return versionOutput.contains("1.") || versionOutput.contains("2.");
        } catch (Exception e) {
            return false;
        }
    }
}
