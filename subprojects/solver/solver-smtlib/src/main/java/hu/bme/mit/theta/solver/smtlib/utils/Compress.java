/*
 *  Copyright 2023 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.solver.smtlib.utils;

import org.apache.commons.compress.archivers.ArchiveEntry;
import org.apache.commons.compress.archivers.ArchiveInputStream;
import org.apache.commons.compress.archivers.tar.TarArchiveInputStream;
import org.apache.commons.compress.archivers.zip.ZipArchiveInputStream;
import org.apache.commons.compress.compressors.gzip.GzipCompressorInputStream;

import java.io.BufferedInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Path;

public class Compress {

    private Compress() {
    }

    public enum CompressionType {
        ZIP, TARGZ
    }

    public static void extract(final InputStream inputStream, final Path extractDir,
                               final CompressionType compressionType) throws IOException {
        switch (compressionType) {
            case ZIP:
                extract(new ZipArchiveInputStream(inputStream), extractDir);
                break;
            case TARGZ:
                extract(new TarArchiveInputStream(
                                new GzipCompressorInputStream(new BufferedInputStream(inputStream))),
                        extractDir);
                break;
            default:
                throw new AssertionError();
        }
    }

    private static void extract(final ArchiveInputStream archiveInputStream, final Path extractDir)
            throws IOException {
        for (ArchiveEntry entry = archiveInputStream.getNextEntry(); entry != null;
             entry = archiveInputStream.getNextEntry()) {
            final var entryPath = Path.of(entry.getName());
            if (entry.isDirectory()) {
                if (entryPath.getNameCount() > 1) {
                    final var entryResolvedPath = extractDir.resolve(
                            entryPath.subpath(1, entryPath.getNameCount()));
                    Files.createDirectories(entryResolvedPath);
                }
            } else {
                final var entryResolvedPath = extractDir.resolve(
                        entryPath.subpath(1, entryPath.getNameCount()));
                Files.createDirectories(entryResolvedPath.getParent());
                Files.copy(archiveInputStream, entryResolvedPath);
            }
        }
    }
}
