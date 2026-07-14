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

import java.io.IOException;
import java.nio.channels.FileChannel;
import java.nio.channels.FileLock;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardOpenOption;
import java.util.Locale;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;
import java.util.concurrent.locks.ReentrantLock;

/**
 * Serializes solver installation/uninstallation across threads <em>and</em> across processes.
 *
 * <p>Installing a solver is not atomic: the install directory is created first and only then
 * populated (downloaded, unpacked, args file written). Without this lock a concurrent reader can
 * observe the directory of an install that is still in flight and conclude the solver is present,
 * then fail when reading files that do not exist yet. A failed install additionally deletes the
 * directory again, which can pull it out from under such a reader.
 *
 * <p>Gradle runs test tasks of different subprojects in parallel, each in its own JVM, all sharing
 * one solver home, so an in-JVM lock alone is not enough — the lock has to live in the file system.
 */
public final class SmtLibSolverInstallLock {

    /**
     * {@link FileLock}s are held per JVM, not per thread: two threads of the same JVM locking the
     * same file raise {@link java.nio.channels.OverlappingFileLockException} instead of waiting for
     * each other. This map serializes them before they reach the file lock.
     */
    private static final ConcurrentMap<String, ReentrantLock> JVM_LOCKS = new ConcurrentHashMap<>();

    private SmtLibSolverInstallLock() {}

    /** An installation step that runs while the lock for a given solver version is held. */
    @FunctionalInterface
    public interface LockedAction<T> {
        T run() throws SmtLibSolverInstallerException;
    }

    /**
     * Runs {@code action} while holding the exclusive lock belonging to {@code solver}/{@code
     * version}. Must not be called re-entrantly for the same solver version.
     */
    public static <T> T withLock(
            final Path home,
            final String solver,
            final String version,
            final LockedAction<T> action)
            throws SmtLibSolverInstallerException {
        final Path lockFile = lockFile(home, solver, version);

        final ReentrantLock jvmLock =
                JVM_LOCKS.computeIfAbsent(lockFile.toString(), key -> new ReentrantLock());
        jvmLock.lock();
        try (FileChannel channel =
                        FileChannel.open(
                                lockFile,
                                StandardOpenOption.CREATE,
                                StandardOpenOption.WRITE,
                                StandardOpenOption.SYNC);
                FileLock fileLock = channel.lock()) {
            return action.run();
        } catch (IOException e) {
            throw new SmtLibSolverInstallerException(
                    String.format("Error acquiring install lock %s: %s", lockFile, e.getMessage()),
                    e);
        } finally {
            jvmLock.unlock();
        }
    }

    /**
     * The lock file lives next to the solver directories rather than inside them, so that it
     * survives the install/uninstall it guards.
     */
    private static Path lockFile(final Path home, final String solver, final String version)
            throws SmtLibSolverInstallerException {
        final Path lockDir = home.resolve(".locks");
        try {
            Files.createDirectories(lockDir);
        } catch (IOException e) {
            throw new SmtLibSolverInstallerException(
                    String.format("Error creating lock directory %s: %s", lockDir, e.getMessage()),
                    e);
        }
        return lockDir.resolve(sanitize(solver) + "-" + sanitize(version) + ".lock");
    }

    private static String sanitize(final String name) {
        return name.toLowerCase(Locale.ROOT).replaceAll("[^a-z0-9._-]", "_");
    }
}
