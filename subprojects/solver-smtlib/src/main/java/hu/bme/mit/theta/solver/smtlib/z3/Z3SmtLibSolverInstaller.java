package hu.bme.mit.theta.solver.smtlib.z3;

import hu.bme.mit.theta.common.OsHelper;
import hu.bme.mit.theta.common.SemVer;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.smtlib.BaseSmtLibSolverInstaller;
import hu.bme.mit.theta.solver.smtlib.SmtLibSolverInstallerException;
import hu.bme.mit.theta.solver.smtlib.generic.GenericSmtLibSolverFactory;

import java.io.IOException;
import java.net.URI;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.common.OsHelper.Architecture.X64;
import static hu.bme.mit.theta.common.OsHelper.Architecture.X86;
import static hu.bme.mit.theta.common.OsHelper.OperatingSystem.LINUX;
import static hu.bme.mit.theta.common.OsHelper.OperatingSystem.MAC;
import static hu.bme.mit.theta.common.OsHelper.OperatingSystem.WINDOWS;

public class Z3SmtLibSolverInstaller extends BaseSmtLibSolverInstaller {
    private final List<VersionDecoder> versions;

    public Z3SmtLibSolverInstaller(final Logger logger) {
        super(logger);

        versions = new ArrayList<>();
        versions.add(VersionDecoder.create(SemVer.of("4.8.5"))
            .addString(LINUX, X64, "x64-ubuntu-16.04")
            .addString(WINDOWS, X64, "x64-win")
            .addString(WINDOWS, X86, "x86-win")
            .addString(MAC, X64, "x64-osx-10.14.6")
            .build()
        );
        versions.add(VersionDecoder.create(SemVer.of("4.8.5"))
            .addString(LINUX, X64, "x64-ubuntu-16.04")
            .addString(WINDOWS, X64, "x64-win")
            .addString(WINDOWS, X86, "x86-win")
            .addString(MAC, X64, "x64-osx-10.14.2")
            .build()
        );
        versions.add(VersionDecoder.create(SemVer.of("4.8.4"))
            .addString(LINUX, X64, "x64-ubuntu-16.04")
            .addString(WINDOWS, X64, "x64-win")
            .addString(WINDOWS, X86, "x86-win")
            .addString(MAC, X64, "x64-osx-10.14.1")
            .build()
        );
        versions.add(VersionDecoder.create(SemVer.of("4.8.3"))
            .addString(LINUX, X64, "x64-ubuntu-16.04")
            .addString(WINDOWS, X64, "x64-win")
            .addString(WINDOWS, X86, "x86-win")
            .addString(MAC, X64, "x64-osx-10.13.6")
            .build()
        );
        versions.add(VersionDecoder.create(SemVer.of("4.6.0"))
            .addString(LINUX, X64, "x64-ubuntu-16.04")
            .addString(WINDOWS, X64, "x64-win")
            .addString(WINDOWS, X86, "x86-win")
            .addString(MAC, X64, "x64-osx-10.11.6")
            .build()
        );
        versions.add(VersionDecoder.create(SemVer.of("4.4.0"))
            .addString(LINUX, X64, "x64-ubuntu-14.04")
            .addString(LINUX, X86, "x86-ubuntu-14.04")
            .addString(WINDOWS, X64, "x64-win")
            .addString(WINDOWS, X86, "x86-win")
            .addString(MAC, X64, "x64-osx-10.11.6")
            .build()
        );
        versions.add(VersionDecoder.create(SemVer.of("4.3.2"))
            .addString(WINDOWS, X64, "x64-win")
            .addString(WINDOWS, X86, "x86-win")
            .build()
        );
    }

    @Override
    protected String getSolverName() {
        return "z3";
    }

    @Override
    protected void installSolver(final Path installDir, final String version) throws SmtLibSolverInstallerException {
        final var semVer = SemVer.of(version);
        String archStr = null;

        for(final var versionDecoder : versions) {
            if(semVer.compareTo(versionDecoder.getVersion()) >= 0) {
                archStr = versionDecoder.getOsArchString(OsHelper.getOs(), OsHelper.getArch());
                break;
            }
        }
        if(archStr == null) {
            throw new SmtLibSolverInstallerException(String.format("z3 on operating system %s and architecture %s is not supported", OsHelper.getOs(), OsHelper.getArch()));
        }

        final var downloadUrl = URI.create(String.format(
            "https://github.com/Z3Prover/z3/releases/download/z3-%s/z3-%s-%s.zip",
            version, version, archStr
        ));

        logger.write(Logger.Level.MAINSTEP, "Starting download (%s)...\n", downloadUrl.toString());
        try(final var zipInputStream = new ZipInputStream(downloadUrl.toURL().openStream())) {
            unzip(zipInputStream, installDir);
            installDir.resolve("bin").resolve(getSolverBinaryName()).toFile().setExecutable(true, true);
        }
        catch (IOException e) {
            throw new SmtLibSolverInstallerException(e);
        }

        logger.write(Logger.Level.MAINSTEP, "Download finished\n");
    }

    @Override
    protected void uninstallSolver(Path installDir, String version) { }

    @Override
    protected String[] getDefaultSolverArgs(String version) {
        return new String[] { "-smt2", "-in" };
    }

    @Override
    public SolverFactory getSolverFactory(final Path home, final String version) throws SmtLibSolverInstallerException {
        checkNotNull(home);
        checkArgument(Files.exists(home));
        checkVersion(version);

        final var installDir = home.resolve(version);
        if(!Files.exists(installDir)) {
            throw new SmtLibSolverInstallerException("The version is not installed");
        }

        try {
            final var solverFilePath = installDir.resolve("bin").resolve(getSolverBinaryName());
            final var solverArgsPath = argsFile(installDir);
            final var solverArgs = Files.readAllLines(solverArgsPath, StandardCharsets.UTF_8).toArray(String[]::new);

            return GenericSmtLibSolverFactory.create(solverFilePath, solverArgs);
        }
        catch (IOException e) {
            throw new SmtLibSolverInstallerException(String.format("Error: %s", e.getMessage()), e);
        }
    }

    @Override
    public List<String> getSupportedVersions() {
        return Arrays.asList(
            "4.8.9", "4.8.8", "4.8.7", "4.8.6", "4.8.5", "4.8.4", "4.8.3", "4.8.2", "4.8.1",
            "4.7.1", "4.6.0", "4.5.0", "4.4.1", "4.4.0", "4.3.2"
        );
    }

    private String getSolverBinaryName() {
        switch(OsHelper.getOs()) {
            case WINDOWS:
                return "z3.exe";
            case LINUX:
                return "z3";
            case MAC:
                return "z3.dmg";
            default:
                throw new AssertionError();
        }
    }

    private static void unzip(final ZipInputStream zipInputStream, final Path installDir) throws SmtLibSolverInstallerException {
        try {
            for(ZipEntry entry = zipInputStream.getNextEntry(); entry != null; entry = zipInputStream.getNextEntry()) {
                final var entryPath = Path.of(entry.getName());
                final var entryResolvedPath = installDir.resolve(entryPath.subpath(1, entryPath.getNameCount()));
                if(entry.isDirectory()) {
                    Files.createDirectories(entryResolvedPath);
                }
                else {
                    Files.createDirectories(entryResolvedPath.getParent());
                    Files.copy(zipInputStream, entryResolvedPath);
                }
            }
        }
        catch(IOException e) {
            throw new SmtLibSolverInstallerException(e.getMessage(), e);
        }
    }

    private static class VersionDecoder {
        private final SemVer version;
        private final Map<OsHelper.OperatingSystem, Map<OsHelper.Architecture, String>> string;

        private VersionDecoder(final SemVer version, final Map<OsHelper.OperatingSystem, Map<OsHelper.Architecture, String>> string) {
            this.version = version;
            this.string = string;
        }

        public static Builder create(final SemVer version) {
            return new Builder(version);
        }

        public SemVer getVersion() {
            return version;
        }

        public String getOsArchString(final OsHelper.OperatingSystem os, final OsHelper.Architecture arch) throws SmtLibSolverInstallerException {
            if(!string.containsKey(os)) {
                throw new SmtLibSolverInstallerException(String.format("Operating system %s is not supported by z3", os));
            }
            else if(!string.get(os).containsKey(arch)) {
                throw new SmtLibSolverInstallerException(String.format("Architecture %s on operating system %s is not supported by z3", arch, os));
            }
            else {
                return string.get(os).get(arch);
            }
        }

        public static class Builder {
            private final SemVer version;
            private final Map<OsHelper.OperatingSystem, Map<OsHelper.Architecture, String>> string;

            private Builder(final SemVer version) {
                this.version = version;
                this.string = new HashMap<>();
            }

            public Builder addString(final OsHelper.OperatingSystem os, final OsHelper.Architecture arch, final String string) {
                if(!this.string.containsKey(os)) {
                    this.string.put(os, new HashMap<>());
                }
                this.string.get(os).put(arch, string);
                return this;
            }

            public VersionDecoder build() {
                return new VersionDecoder(version, string);
            }
        }
    }
}
