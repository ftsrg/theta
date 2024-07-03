/*
 *  Copyright 2024 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.solver.smtlib.impl.smtinterpol;

import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.smtlib.solver.installer.SmtLibSolverInstaller;
import hu.bme.mit.theta.solver.smtlib.solver.installer.SmtLibSolverInstallerException;

import java.io.FileOutputStream;
import java.io.IOException;
import java.net.MalformedURLException;
import java.net.URI;
import java.net.URL;
import java.nio.channels.Channels;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.List;

public class SMTInterpolSmtLibSolverInstaller extends SmtLibSolverInstaller.Default {

    public SMTInterpolSmtLibSolverInstaller(final Logger logger) {
        super(logger);
    }

    @Override
    protected String getSolverName() {
        return "smtinterpol";
    }

    @Override
    protected void installSolver(final Path installDir, final String version)
            throws SmtLibSolverInstallerException {

        try (
                final var inputChannel = Channels.newChannel(getDownloadUrl(version).openStream());
                final var outputChannel = new FileOutputStream(
                        installDir.resolve(getSolverBinaryName(version)).toAbsolutePath()
                                .toString()).getChannel()
        ) {
            logger.write(Logger.Level.MAINSTEP, "Starting download (%s)...\n",
                    getDownloadUrl(version).toString());
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
        return new String[]{"-smt2", "-q"};
    }

    @Override
    public SolverFactory getSolverFactory(final Path installDir, final String version,
                                          final Path solverPath, final String[] solverArgs) throws SmtLibSolverInstallerException {
        final var solverFilePath =
                solverPath != null ? solverPath : installDir.resolve(getSolverBinaryName(version));
        return SMTInterpolSmtLibSolverFactory.create(solverFilePath, solverArgs);
    }

    @Override
    public List<String> getSupportedVersions() {
        return Arrays.asList("2.5-1256", "2.5-1230", "2.5-916", "2.5-663", "2.5-479", "2.5-7");
    }

    private URL getDownloadUrl(final String version)
            throws SmtLibSolverInstallerException, MalformedURLException {
        final String fileName;
        switch (version) {
            case "2.5-1256":
                fileName = "2.5-1256-g55d6ba76";
                break;
            case "2.5-1230":
                fileName = "2.5-1230-g3eafb46a";
                break;
            case "2.5-916":
                fileName = "2.5-916-ga5843d8b";
                break;
            case "2.5-663":
                fileName = "2.5-663-gf15aa217";
                break;
            case "2.5-479":
                fileName = "2.5-479-ga49e50b1";
                break;
            case "2.5-7":
                fileName = "2.5-7-g64ec65d";
                break;
            default:
                throw new SmtLibSolverInstallerException("Unsupported solver version.");
        }

        return URI.create(String.format(
                "https://ultimate.informatik.uni-freiburg.de/smtinterpol/smtinterpol-%s.jar",
                fileName
        )).toURL();
    }

    private String getSolverBinaryName(final String version) {
        return String.format("smtinterpol-%s.jar", version);
    }
}
