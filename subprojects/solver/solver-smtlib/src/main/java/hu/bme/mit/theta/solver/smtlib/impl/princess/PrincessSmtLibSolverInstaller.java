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
package hu.bme.mit.theta.solver.smtlib.impl.princess;

import hu.bme.mit.theta.common.OsHelper;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.smtlib.solver.installer.SmtLibSolverInstaller;
import hu.bme.mit.theta.solver.smtlib.solver.installer.SmtLibSolverInstallerException;
import hu.bme.mit.theta.solver.smtlib.utils.Compress;

import java.io.IOException;
import java.net.URI;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.List;

public class PrincessSmtLibSolverInstaller extends SmtLibSolverInstaller.Default {

    public PrincessSmtLibSolverInstaller(final Logger logger) {
        super(logger);
    }

    @Override
    protected String getSolverName() {
        return "princess";
    }

    @Override
    protected void installSolver(final Path installDir, final String version)
            throws SmtLibSolverInstallerException {

        final var downloadUrl = Integer.parseInt(version.substring(0, 4)) > 2021 ?
                URI.create(String.format(
                        "https://github.com/uuverifiers/princess/releases/download/snapshot-%s/princess-bin-%s.zip",
                        version, version
                )) :
                URI.create(String.format(
                        "http://www.philipp.ruemmer.org/princess/princess-bin-%s.zip",
                        version
                ));

        logger.write(Logger.Level.MAINSTEP, "Starting download (%s)...\n", downloadUrl.toString());

        try (final var inputStream = downloadUrl.toURL().openStream()) {
            Compress.extract(inputStream, installDir, Compress.CompressionType.ZIP);
            installDir.resolve(getSolverBinaryName()).toFile().setExecutable(true, true);
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
        return new String[]{
                "+stdin",
                "+incremental",
                "+quiet"
        };
    }

    @Override
    public SolverFactory getSolverFactory(final Path installDir, final String version,
                                          final Path solverPath, final String[] solverArgs) throws SmtLibSolverInstallerException {
        final var solverFilePath =
                solverPath != null ? solverPath : installDir.resolve(getSolverBinaryName());
        return PrincessSmtLibSolverFactory.create(solverFilePath, solverArgs);
    }

    @Override
    public List<String> getSupportedVersions() {
        return Arrays.asList(
                "2022-07-01", "2021-11-15",
                "2021-05-10", "2021-03-10", "2020-03-12", "2019-10-02", "2019-07-24",
                "2018-10-26", "2018-05-25", "2018-01-27", "2017-12-06", "2017-07-17"
        );
    }

    private String getSolverBinaryName() {
        switch (OsHelper.getOs()) {
            case WINDOWS:
                return "princess.bat";
            case MAC:
            case LINUX:
                return "princess";
            default:
                throw new AssertionError();
        }
    }
}
