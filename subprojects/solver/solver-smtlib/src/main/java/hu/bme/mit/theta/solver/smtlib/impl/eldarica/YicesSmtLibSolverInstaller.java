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
import java.io.BufferedInputStream;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.net.URI;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Comparator;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/*
This is a dependency of Eldarica which is not included in the binary.
 */
public class YicesSmtLibSolverInstaller extends SmtLibSolverInstaller.Default {

    private final List<SemVer.VersionDecoder> versions;

    private static final String YICES_VERSION = "1.0.40";
    private static final String GITHUB_DOWNLOAD =
            "https://github.com/SRI-CSL/yices2/releases/download/Yices-2.6.5/yices-2.6.5-x86_64-pc-linux-gnu-static-gmp.tar.gz";
    private static final String SRI_DOWNLOAD =
            "http://yices.csl.sri.com/old/binaries/yices-1.0.40-x86_64-unknown-linux-gnu-static-gmp.tar.gz";

    public YicesSmtLibSolverInstaller() {

        versions = new ArrayList<>();
        versions.add(
                SemVer.VersionDecoder.create(SemVer.of("2.1"))
                        .addString(LINUX, X64, "zip")
                        .build());
    }

    @Override
    protected String getSolverName() {
        return "yices";
    }

    @Override
    protected void installSolver(final Path installDir, final String version)
            throws SmtLibSolverInstallerException {
        Logger.mainStep("Starting download attempt for Yices %s...\n", version);
        final var candidates = Arrays.asList(GITHUB_DOWNLOAD, SRI_DOWNLOAD);
        final List<String> failures = new ArrayList<>();

        for (final var candidate : candidates) {
            try {
                installFromCandidate(installDir, candidate);
                Logger.mainStep("Download finished\n");
                return;
            } catch (Exception e) {
                final var message = e.getMessage() == null ? e.toString() : e.getMessage();
                failures.add(candidate + " (" + message + ")");
                Logger.yicesolver("Candidate %s failed: %s", candidate, message);
            }
        }

        throw new SmtLibSolverInstallerException(
                "Unable to install a compatible Yices binary from mirrors: "
                        + String.join("; ", failures));
    }

    @Override
    protected void uninstallSolver(Path installDir, String version) {
        // Default uninstall is suitable
    }

    @Override
    protected SolverFactory getSolverFactory(
            Path installDir, String version, Path solverPath, String[] args)
            throws SmtLibSolverInstallerException {
        throw new UnsupportedOperationException("Yices cannot be started.");
    }

    @Override
    protected String[] getDefaultSolverArgs(String version) {
        return new String[] {};
    }

    @Override
    public List<String> getSupportedVersions() {
        return Arrays.asList(YICES_VERSION);
    }

    private String getSolverBinaryName() {
        switch (OsHelper.getOs()) {
            case LINUX:
                return "yices";
            default:
                throw new AssertionError();
        }
    }

    private void installFromCandidate(final Path installDir, final String candidate)
            throws IOException, InterruptedException, SmtLibSolverInstallerException {
        cleanupInstallDir(installDir);
        Logger.yicesolver("Trying Yices download from %s", candidate);
        try (InputStream inputStream = new BufferedInputStream(URI.create(candidate).toURL().openStream())) {
            Compress.extract(inputStream, installDir, Compress.CompressionType.TARGZ);
        }

        final var yicesBinary = installDir.resolve("bin").resolve(getSolverBinaryName());
        if (!Files.exists(yicesBinary)) {
            throw new SmtLibSolverInstallerException(
                    "Downloaded archive does not contain " + yicesBinary);
        }
        yicesBinary.toFile().setExecutable(true, true);

        final var versionOutput = readVersion(yicesBinary);
        if (!versionOutput.contains("1.")) {
            Logger.yicesolver(
                    "Downloaded Yices version is not 1.x (%s); proceeding as fallback", versionOutput);
        }
        Logger.yicesolver("Installed Yices from %s (%s)", candidate, versionOutput);
    }

    private String readVersion(final Path yicesBinary) throws IOException, InterruptedException {
        final var process = new ProcessBuilder(yicesBinary.toAbsolutePath().toString(), "--version").start();
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
        return output.toString().trim();
    }

    private void cleanupInstallDir(final Path installDir) throws IOException {
        if (!Files.exists(installDir)) {
            return;
        }
        try (final var paths = Files.walk(installDir)) {
            paths.sorted(Comparator.reverseOrder())
                    .forEach(
                            path -> {
                                try {
                                    Files.delete(path);
                                } catch (IOException e) {
                                    throw new RuntimeException(e);
                                }
                            });
        } catch (RuntimeException e) {
            if (e.getCause() instanceof IOException) {
                throw (IOException) e.getCause();
            }
            throw e;
        }
    }
}
