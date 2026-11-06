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
package hu.bme.mit.theta.solver.smtlib.impl.generic;

import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assumptions.assumeTrue;

import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.attribute.PosixFilePermissions;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

public class GenericSmtLibSolverBinaryTest {

    @Test
    public void startFailureNamesTheBinary(@TempDir final Path dir) throws Exception {
        assumeTrue(FileSystems.getDefault().supportedFileAttributeViews().contains("posix"));
        final Path solver = dir.resolve("solver");
        Files.writeString(solver, "#!/bin/sh\ncat\n");

        Files.setPosixFilePermissions(solver, PosixFilePermissions.fromString("rw-r--r--"));
        final var failure =
                assertThrows(
                        IllegalStateException.class,
                        () -> new GenericSmtLibSolverBinary(solver, new String[] {}));
        final String message = String.valueOf(failure.getMessage());
        assertTrue(message.contains(solver.toString()), message);
        assertTrue(message.contains("not executable"), message);

        Files.setPosixFilePermissions(solver, PosixFilePermissions.fromString("rwxr-xr-x"));
        new GenericSmtLibSolverBinary(solver, new String[] {}).close();
    }
}
