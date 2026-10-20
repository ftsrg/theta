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
package hu.bme.mit.theta.solver.smtlib.impl.mathsat;

import static org.junit.jupiter.api.Assertions.assertEquals;

import hu.bme.mit.theta.common.logging.NullLogger;
import hu.bme.mit.theta.solver.smtlib.solver.installer.SmtLibSolverInstallerException;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

/** Checks the archive URLs, simulating each platform via the properties OsHelper reads. */
public class MathSATSmtLibSolverInstallerTest {

    private final MathSATSmtLibSolverInstaller installer =
            new MathSATSmtLibSolverInstaller(NullLogger.getInstance());

    private String savedOsName;
    private String savedOsArch;

    @BeforeEach
    public void saveOs() {
        savedOsName = System.getProperty("os.name");
        savedOsArch = System.getProperty("os.arch");
    }

    @AfterEach
    public void restoreOs() {
        System.setProperty("os.name", savedOsName);
        System.setProperty("os.arch", savedOsArch);
    }

    private String urlOn(final String osName, final String version)
            throws SmtLibSolverInstallerException {
        System.setProperty("os.name", osName);
        System.setProperty("os.arch", "amd64");
        return installer.getDownloadUrl(version).toString();
    }

    @Test
    public void windowsArchiveNames() throws SmtLibSolverInstallerException {
        final String latest = installer.getSupportedVersions().get(0);
        assertEquals(
                "https://mathsat.fbk.eu/release/mathsat-" + latest + "-win64.zip",
                urlOn("Windows 10", latest));
        assertEquals(
                "https://mathsat.fbk.eu/release/mathsat-5.6.12-win64.zip",
                urlOn("Windows 10", "5.6.12"));
        assertEquals(
                "https://mathsat.fbk.eu/release/mathsat-5.6.11-win64-msvc.zip",
                urlOn("Windows 10", "5.6.11"));
        assertEquals(
                "https://mathsat.fbk.eu/release/mathsat-5.6.10-win64-msvc.zip",
                urlOn("Windows 10", "5.6.10"));
    }

    @Test
    public void linuxAndMacArchiveNames() throws SmtLibSolverInstallerException {
        assertEquals(
                "https://mathsat.fbk.eu/release/mathsat-5.6.12-linux-x86_64.tar.gz",
                urlOn("Linux", "5.6.12"));
        assertEquals(
                "https://mathsat.fbk.eu/release/mathsat-5.6.12-macos.tar.gz",
                urlOn("Mac OS X", "5.6.12"));
        assertEquals(
                "https://mathsat.fbk.eu/release/mathsat-5.6.11-osx.tar.gz",
                urlOn("Mac OS X", "5.6.11"));
    }
}
