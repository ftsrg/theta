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
package hu.bme.mit.theta.solver.smtlib.testing;

import hu.bme.mit.theta.common.OsHelper;
import hu.bme.mit.theta.common.logging.NullLogger;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.smtlib.SmtLibSolverManager;
import java.io.IOException;
import java.nio.channels.FileChannel;
import java.nio.channels.FileLock;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardOpenOption;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import org.junit.jupiter.api.Assumptions;

/**
 * Single entry point for tests that need an SMT-LIB solver to be installed.
 *
 * <p>Installation is idempotent and locked (see {@code SmtLibSolverInstallLock}), so parallel test
 * tasks neither race nor reinstall. Solvers are deliberately <em>never</em> uninstalled: they are a
 * cache, and tearing them down only forces the next run to download them again — and, when tasks
 * run in parallel, pulls them out from under a test that is still using them.
 *
 * <p>When a solver cannot be installed the affected tests are skipped rather than reported as
 * failures, since the cause is environmental (no network, changed download URL, unsupported
 * platform). To keep such a run from passing silently, every skip is recorded, and the {@code
 * verifySolverInstallations} Gradle task fails the build afterwards. Under GitHub Actions the
 * failures are additionally written to the job summary.
 */
public final class SolverInstallations {

    /** Set by the build to the file this JVM records its installation failures in. */
    private static final String REPORT_PROPERTY = "theta.solverInstallFailureReport";

    private static final Set<String> reported = ConcurrentHashMap.newKeySet();

    private static volatile SmtLibSolverManager manager;

    private SolverInstallations() {}

    /**
     * Ensures {@code version} of {@code solver} is installed and returns a factory for it. Skips
     * the calling test (or the whole class, when called from {@code @BeforeAll}) if it cannot be
     * installed.
     */
    public static SolverFactory installOrSkip(final String solver, final String version) {
        Assumptions.assumeTrue(
                OsHelper.getOs() == OsHelper.OperatingSystem.LINUX,
                "SMT-LIB solvers are only installed on Linux");

        try {
            final SmtLibSolverManager solverManager = manager();
            solverManager.installIfMissing(solver, version);
            return solverManager.getSolverFactory(solver, version);
        } catch (Exception e) {
            final String name = solver + ":" + version;
            recordFailure(name, e);
            // Skip rather than fail: verifySolverInstallations turns this into a build failure.
            Assumptions.assumeTrue(false, "Could not install solver " + name + ": " + e);
            throw new AssertionError("unreachable");
        }
    }

    /** As {@link #installOrSkip(String, String)}, for a combined {@code "z3:4.13.0"} name. */
    public static SolverFactory installOrSkip(final String solverAndVersion) {
        return installOrSkip(
                SmtLibSolverManager.getSolverName(solverAndVersion),
                SmtLibSolverManager.getSolverVersion(solverAndVersion));
    }

    /** The shared manager over the real solver home. Never closed: it owns no solver instances. */
    public static SmtLibSolverManager manager() throws Exception {
        SmtLibSolverManager local = manager;
        if (local == null) {
            synchronized (SolverInstallations.class) {
                local = manager;
                if (local == null) {
                    local =
                            SmtLibSolverManager.create(
                                    SmtLibSolverManager.HOME, NullLogger.getInstance());
                    manager = local;
                }
            }
        }
        return local;
    }

    private static void recordFailure(final String solver, final Exception cause) {
        if (!reported.add(solver)) {
            return; // one report per solver per JVM is enough
        }

        final String message = solver + " — " + cause;
        System.err.println("[solver-install] FAILED to install " + message);

        final String report = System.getProperty(REPORT_PROPERTY);
        if (report != null) {
            appendLine(Path.of(report), message);
        }

        final String stepSummary = System.getenv("GITHUB_STEP_SUMMARY");
        if (stepSummary != null && !stepSummary.isBlank()) {
            appendLine(
                    Path.of(stepSummary),
                    "- :x: **Solver installation failed:** `" + solver + "` — " + cause);
        }
    }

    /**
     * Appends one line, holding an exclusive file lock: several test JVMs share both the report
     * file and the GitHub step summary, and their writes must not interleave.
     */
    private static void appendLine(final Path file, final String line) {
        try {
            final Path parent = file.toAbsolutePath().getParent();
            if (parent != null) {
                Files.createDirectories(parent);
            }
            try (FileChannel channel =
                            FileChannel.open(
                                    file, StandardOpenOption.CREATE, StandardOpenOption.WRITE);
                    FileLock ignored = channel.lock()) {
                channel.position(channel.size());
                channel.write(StandardCharsets.UTF_8.encode(line + System.lineSeparator()));
            }
        } catch (IOException e) {
            System.err.println("[solver-install] could not write " + file + ": " + e);
        }
    }
}
