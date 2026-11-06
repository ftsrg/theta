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
package hu.bme.mit.theta.solver.smtlib.solver.installer;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assumptions.assumeTrue;

import hu.bme.mit.theta.common.logging.NullLogger;
import hu.bme.mit.theta.solver.SolverFactory;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.attribute.PosixFileAttributeView;
import java.nio.file.attribute.PosixFilePermissions;
import java.util.List;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

public class SmtLibSolverInstallerTest {

    private static final String BINARY = "solver-binary";

    @TempDir Path home;

    /** A solver installed by one user must be runnable by others (e.g., in a container). */
    @Test
    public void installedBinaryIsExecutableByEveryone() throws Exception {
        assumeTrue(
                Files.getFileStore(home).supportsFileAttributeView(PosixFileAttributeView.class),
                "POSIX file permissions are not supported here");

        new FakeInstaller().install(home, "1.0", "1.0");

        assertEquals(
                PosixFilePermissions.fromString("rwxr-xr-x"),
                Files.getPosixFilePermissions(home.resolve("1.0").resolve(BINARY)));
    }

    private static final class FakeInstaller extends SmtLibSolverInstaller.Default {

        FakeInstaller() {
            super(NullLogger.getInstance());
        }

        @Override
        protected String getSolverName() {
            return "fake";
        }

        @Override
        protected void installSolver(final Path installDir, final String version)
                throws SmtLibSolverInstallerException {
            final var binary = installDir.resolve(BINARY);
            try {
                Files.createFile(binary);
                Files.setPosixFilePermissions(binary, PosixFilePermissions.fromString("rw-r--r--"));
            } catch (IOException e) {
                throw new SmtLibSolverInstallerException(e);
            }
            makeExecutable(binary);
        }

        @Override
        protected void uninstallSolver(final Path installDir, final String version) {}

        @Override
        protected SolverFactory getSolverFactory(
                final Path installDir,
                final String version,
                final Path solverPath,
                final String[] args) {
            throw new UnsupportedOperationException();
        }

        @Override
        protected String[] getDefaultSolverArgs(final String version) {
            return new String[0];
        }

        @Override
        public List<String> getSupportedVersions() {
            return List.of("1.0");
        }
    }
}
