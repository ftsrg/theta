package hu.bme.mit.theta.solver.smtlib.cli;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParameterException;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.solver.smtlib.SmtLibSolverInstallerException;
import hu.bme.mit.theta.solver.smtlib.manager.SmtLibSolverManager;

import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.nio.file.Files;
import java.nio.file.Path;

public class SmtLibCli {
    private static final String JAR_NAME = "theta-solver-smtlib-cli.jar";
    private final String[] args;

    private Logger logger;

    @Parameter(names = "--install", description = "Install a solver")
    String install;

    @Parameter(names = "--install-solverPath", description = "The path of the generic solver to install")
    String installSolverPath;

    @Parameter(names = "--install-solverArgs", description = "The arguments of the generic solver to invoke with")
    String installSolverArgs;

    @Parameter(names = "--uninstall", description = "Uninstall a solver")
    String uninstall;

    @Parameter(names = "--list-installed", description = "Lists installed solvers and their versions")
    private boolean listInstalled;

    @Parameter(names = "--home", description = "The path of the solver registry")
    String home = Path.of(System.getProperty("user.home"), ".theta").toAbsolutePath().toString();

    @Parameter(names = "--loglevel", description = "Detailedness of logging")
    Logger.Level logLevel = Logger.Level.MAINSTEP;

    @Parameter(names = "--help", help = true)
    private boolean help;

    public SmtLibCli(final String[] args) {
        this.args = args;
    }

    public static void main(final String[] args) {
        final SmtLibCli mainApp = new SmtLibCli(args);
        mainApp.run();
    }

    private void run() {
        final var jc = JCommander.newBuilder().addObject(this).programName(JAR_NAME).build();
        try {
            jc.parse(args);
            logger = new ConsoleLogger(logLevel);
        } catch (final ParameterException ex) {
            System.out.println("Invalid parameters, details:");
            System.out.println(ex.getMessage());
            ex.usage();
            return;
        }

        if(help) {
            jc.usage();
            return;
        }

        if(!isExactlyOneGiven(install, uninstall, listInstalled ? true : null)) {
            jc.usage();
            return;
        }

        if(install == null && (installSolverPath != null || installSolverArgs != null)) {
            jc.usage();
            return;
        }

        try {
            final var homePath = createIfNotExists(Path.of(home));
            final var smtLibSolverManager = SmtLibSolverManager.create(homePath, logger);

            if (install != null) {
                final var solver = decodeVersionString(install, smtLibSolverManager);
                if(solver.get1().equals(smtLibSolverManager.getGenericInstallerName())) {
                    if(installSolverPath == null) {
                        jc.usage();
                        return;
                    }

                    smtLibSolverManager.installGeneric(
                        solver.get2(),
                        Path.of(installSolverPath),
                        (installSolverArgs == null ? "" : installSolverArgs).split(" ")
                    );
                }
                else {
                    smtLibSolverManager.install(solver.get1(), solver.get2());
                }
            }
            else if(uninstall != null) {
                final var solver = decodeVersionString(uninstall, smtLibSolverManager);
                smtLibSolverManager.uninstall(solver.get1(), solver.get2());
            }
            else if(listInstalled) {
                logger.write(Logger.Level.RESULT, "The currently installed solvers are: \n");
                smtLibSolverManager.getInstalledVersions().forEach(solver -> {
                    solver.get2().forEach(version -> {
                        logger.write(Logger.Level.RESULT, "\t%s:%s\n", solver.get1(), version);
                    });
                });
            }
        } catch (SmtLibSolverInstallerException | IOException e) {
            printError(e);
        }
    }

    private boolean isExactlyOneGiven(final Object ...args) {
        int count = 0;
        for(final var arg : args) {
            if(arg != null) count++;
        }
        return count == 1;
    }

    private Tuple2<String, String> decodeVersionString(final String version, final SmtLibSolverManager solverManager) throws SmtLibSolverInstallerException {
        final var versionArr = version.split(":");

        if(versionArr.length != 1 && versionArr.length != 2) {
            throw new IllegalArgumentException("Invalid version string: " + version);
        }

        final var solver = versionArr[0];
        if(versionArr.length == 2) {
            return Tuple2.of(solver, versionArr[1]);
        }
        else {
            final var versions = solverManager.getSupportedVersions(solver);
            if(versions.size() > 0) {
                return Tuple2.of(solver, versions.get(0));
            }
            else {
                throw new IllegalArgumentException("Invalid version string: " + version);
            }
        }
    }

    private Path createIfNotExists(final Path path) throws IOException {
        if(!Files.exists(path)) {
            Files.createDirectory(path);
        }
        return path;
    }

    private void printError(final Throwable ex) {
        final String message = ex.getMessage() == null ? "" : ": " + ex.getMessage();
        logger.write(Logger.Level.RESULT, "Exception of type %s occurred%n", ex.getClass().getSimpleName());
        logger.write(Logger.Level.MAINSTEP, "Message:%n%s%n", ex.getMessage());
        final StringWriter errors = new StringWriter();
        ex.printStackTrace(new PrintWriter(errors));
        logger.write(Logger.Level.SUBSTEP, "Trace:%n%s%n", errors.toString());
    }
}
