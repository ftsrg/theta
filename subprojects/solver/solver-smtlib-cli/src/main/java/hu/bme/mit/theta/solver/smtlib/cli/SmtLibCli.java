package hu.bme.mit.theta.solver.smtlib.cli;

import com.beust.jcommander.IParameterValidator;
import com.beust.jcommander.JCommander;
import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParameterException;
import com.beust.jcommander.Parameters;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.solver.smtlib.solver.installer.SmtLibSolverInstallerException;
import hu.bme.mit.theta.solver.smtlib.SmtLibSolverManager;

import java.awt.Desktop;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

public class SmtLibCli {
    private static final String JAR_NAME = "theta-solver-smtlib-cli.jar";
    private final String[] args;

    private Logger logger;

    static class MainParams {
        @Parameter(names = "--home", description = "The path of the solver registry")
        String home = SmtLibSolverManager.HOME.toAbsolutePath().toString();

        @Parameter(names = "--loglevel", description = "Detailedness of logging")
        Logger.Level logLevel = Logger.Level.MAINSTEP;

        @Parameter(names = "--stacktrace", description = "Prints the stacktrace in case of an error")
        private boolean stacktrace = false;

        @Parameter(names = "--help", help = true, description = "Prints this help message")
        private boolean help = false;
    }

    interface Command {
        String getCommand();
        void handle(SmtLibSolverManager smtLibSolverManager, Logger logger) throws SmtLibSolverInstallerException;
    }

    @Parameters(commandDescription = "Installs the solver")
    static class InstallCommand implements Command {
        static final String COMMAND = "install";

        @Parameter(description = "The solver to install (<solver_name>:<solver_version>)", validateWith = SolverNameAndVersionValidator.class, required = true)
        String solver;

        @Parameter(names = "--name", description = "Install the solver version under this custom name (<solver_name>:<name>), instead of the default (<solver_name>:<solver_version>)")
        String name;

        @Parameter(names = "--solver-path", description = "The path of the solver to install. The solver will not be downloaded, instead the binary on this path will be used. Caveat emptor: the version must be specified correctly, there is no automatic detection.")
        String solverPath;

        @Parameter(names = "--tempt-murphy", description = "Allows the installation of unsupported solver version")
        boolean temptMurphy = false;
        
        @Override
        public String getCommand() {
            return COMMAND;
        }

        @Override
        public void handle(final SmtLibSolverManager smtLibSolverManager, final Logger logger) throws SmtLibSolverInstallerException{
            final var solver = decodeVersionString(this.solver);

            if(solver.get1().equals(smtLibSolverManager.getGenericInstallerName())) {
                logger.write(Logger.Level.RESULT, "To install a generic solver, use the \"%s\" command", InstallGenericCommand.COMMAND);
                return;
            }

            if(name != null) {
                smtLibSolverManager.install(solver.get1(), solver.get2(), name, solverPath != null ? Path.of(solverPath) : null, temptMurphy);
            }
            else {
                smtLibSolverManager.install(solver.get1(), solver.get2(), solver.get2(), solverPath != null ? Path.of(solverPath) : null, temptMurphy);
            }
        }
    }

    @Parameters(commandDescription = "Installs a generic solver")
    static class InstallGenericCommand implements Command {
        static final String COMMAND = "install-generic";

        @Parameter(names = "--solver-path", description = "The path of the generic solver to install", required = true)
        String solverPath;

        @Parameter(names = "--solver-args", description = "The arguments of the generic solver to invoke with")
        String solverArgs;

        @Parameter(names = "--name", description = "Install the solver version under this custom name (<solver_name>:<name>), instead of the default (<solver_name>:<solver_version>)", required = true)
        String name;

        @Override
        public String getCommand() {
            return COMMAND;
        }

        @Override
        public void handle(final SmtLibSolverManager smtLibSolverManager, final Logger logger) throws SmtLibSolverInstallerException {
            smtLibSolverManager.installGeneric(
                name,
                Path.of(solverPath),
                (solverArgs == null ? "" : solverArgs).split(" ")
            );
        }
    }

    @Parameters(commandDescription = "Uninstalls the solver")
    static class UninstallCommand implements Command {
        static final String COMMAND = "uninstall";

        @Parameter(description = "The solver to uninstall (<solver_name>:<solver_version>)", validateWith = SolverNameAndVersionValidator.class, required = true)
        String solver;

        @Override
        public String getCommand() {
            return COMMAND;
        }

        @Override
        public void handle(SmtLibSolverManager smtLibSolverManager, Logger logger) throws SmtLibSolverInstallerException {
            final var solver = decodeVersionString(this.solver);
            smtLibSolverManager.uninstall(solver.get1(), solver.get2());
        }
    }

    @Parameters(commandDescription = "Renames one installed solver version")
    static class RenameCommand implements Command {
        static final String COMMAND = "rename";

        @Parameter(description = "The solver to reinstall (<solver_name>:<solver_version>)", validateWith = SolverNameAndVersionValidator.class, required = true)
        String solver;

        @Parameter(names = "--name", description = "Rename the solver version to this custom name (<solver_name>:<name>).", required = true)
        String name;

        @Override
        public String getCommand() {
            return COMMAND;
        }

        @Override
        public void handle(SmtLibSolverManager smtLibSolverManager, Logger logger) throws SmtLibSolverInstallerException {
            final var solver = decodeVersionString(this.solver);
            smtLibSolverManager.rename(solver.get1(), solver.get2(), name);
        }
    }

    @Parameters(commandDescription = "Prints info about the solver")
    static class GetInfoCommand implements Command {
        static final String COMMAND = "get-info";

        @Parameter(description = "The solver to print info about (<solver_name>:<solver_version>)", validateWith = SolverNameAndVersionValidator.class, required = true)
        String solver;

        @Override
        public String getCommand() {
            return COMMAND;
        }

        @Override
        public void handle(SmtLibSolverManager smtLibSolverManager, Logger logger) throws SmtLibSolverInstallerException {
            final var solver = decodeVersionString(this.solver);
            final var info = smtLibSolverManager.getInfo(solver.get1(), solver.get2());
            logger.write(Logger.Level.RESULT, "%s\n", info);
        }
    }

    @Parameters(commandDescription = "Edits the runtime arguments passed to the solver")
    static class EditArgsCommand implements Command {
        static final String COMMAND = "edit-args";

        @Parameter(description = "The solver, whose runtime arguments are to be edited (<solver_name>:<solver_version>)", validateWith = SolverNameAndVersionValidator.class, required = true)
        String solver;

        @Parameter(names = "--print", description = "Print the path instead of opening it for editing")
        boolean print = false;

        @Override
        public String getCommand() {
            return COMMAND;
        }

        @Override
        public void handle(SmtLibSolverManager smtLibSolverManager, Logger logger) throws SmtLibSolverInstallerException {
            final var solver = decodeVersionString(this.solver);
            final var argsFilePath = smtLibSolverManager.getArgsFile(solver.get1(), solver.get2());

            if(print) {
                logger.write(Logger.Level.RESULT, String.format("%s\n", argsFilePath.toAbsolutePath()));
            }
            else if(Desktop.isDesktopSupported() && Desktop.getDesktop().isSupported(Desktop.Action.EDIT)) {
                try {
                    Desktop.getDesktop().edit(argsFilePath.toFile());
                } catch (IOException e) {
                    throw new SmtLibSolverInstallerException(e);
                }
            }
            else {
                logger.write(Logger.Level.MAINSTEP, "Open the following text file in your favourite editor, and edit the content:\n");
                logger.write(Logger.Level.RESULT, String.format("%s\n", argsFilePath.toAbsolutePath()));
            }
        }
    }

    @Parameters(commandDescription = "Lists installed solvers and their versions")
    static class ListInstalledCommand implements Command {
        static final String COMMAND = "list-installed";

        @Parameter(description = "The solver, whose installed versions are to be listed (<solver_name>)", validateWith = SolverNameValidator.class)
        String solver;

        @Override
        public String getCommand() {
            return COMMAND;
        }

        @Override
        public void handle(SmtLibSolverManager smtLibSolverManager, Logger logger) throws SmtLibSolverInstallerException {
            if(solver != null) {
                logger.write(Logger.Level.MAINSTEP, "The currently installed versions of solver %s are: \n", solver);
                smtLibSolverManager.getInstalledVersions(solver).forEach(version -> {
                    logger.write(Logger.Level.RESULT, "\t%s:%s\n", solver, version);
                });
            }
            else {
                logger.write(Logger.Level.MAINSTEP, "The currently installed solvers are: \n");
                smtLibSolverManager.getInstalledVersions().forEach(solver -> {
                    solver.get2().forEach(version -> {
                        logger.write(Logger.Level.RESULT, "\t%s:%s\n", solver.get1(), version);
                    });
                });
            }
        }
    }

    @Parameters(commandDescription = "Lists supported solvers and their versions")
    static class ListSupportedCommand implements Command {
        static final String COMMAND = "list-supported";

        @Parameter(description = "The solver, whose supported versions are to be listed (<solver_name>)", validateWith = SolverNameValidator.class)
        String solver;

        @Override
        public String getCommand() {
            return COMMAND;
        }

        @Override
        public void handle(SmtLibSolverManager smtLibSolverManager, Logger logger) throws SmtLibSolverInstallerException {
            if(solver != null) {
                logger.write(Logger.Level.MAINSTEP, "The currently supported versions of solver %s are: \n", solver);
                smtLibSolverManager.getSupportedVersions(solver).forEach(version -> {
                    logger.write(Logger.Level.RESULT, "\t%s:%s\n", solver, version);
                });
            }
            else {
                logger.write(Logger.Level.MAINSTEP, "The currently supported solvers are: \n");
                smtLibSolverManager.getSupportedVersions().forEach(solver -> {
                    solver.get2().forEach(version -> {
                        logger.write(Logger.Level.RESULT, "\t%s:%s\n", solver.get1(), version);
                    });
                });
            }
        }
    }

    public SmtLibCli(final String[] args) {
        this.args = args;
    }

    public static void main(final String[] args) {
        final SmtLibCli mainApp = new SmtLibCli(args);
        mainApp.run();
    }

    private void run() {
        final var mainParams = new MainParams();
        List<Command> commands = List.of(
            new InstallCommand(),
            new InstallGenericCommand(),
            new UninstallCommand(),
            new RenameCommand(),
            new GetInfoCommand(),
            new EditArgsCommand(),
            new ListInstalledCommand(),
            new ListSupportedCommand()
        );

        final var jcBuilder = JCommander.newBuilder().addObject(mainParams);
        commands.forEach(command -> jcBuilder.addCommand(command.getCommand(), command));
        final var jc = jcBuilder.programName(JAR_NAME).build();

        try {
            jc.parse(args);
            logger = new ConsoleLogger(mainParams.logLevel);
        } catch (final ParameterException ex) {
            System.out.println("Invalid parameters, details:");
            System.out.println(ex.getMessage());
            ex.usage();
            return;
        }

        if(mainParams.help) {
            jc.usage();
            return;
        }

        try {
            final var homePath = createIfNotExists(Path.of(mainParams.home));
            final var smtLibSolverManager = SmtLibSolverManager.create(homePath, logger);

            if(jc.getParsedCommand() == null) {
                logger.write(Logger.Level.RESULT, "Missing command\n");
                jc.usage();
                return;
            }

            final var parsedCommand = jc.getParsedCommand();
            for(final var command : commands) {
                if(command.getCommand().equals(parsedCommand)) {
                    command.handle(smtLibSolverManager, logger);
                    return;
                }
            }
            logger.write(Logger.Level.RESULT, "Unknown command\n");
            jc.usage();
        }
        catch (SmtLibSolverInstallerException e) {
            logger.write(Logger.Level.RESULT, "%s\n", e.getMessage());
            if(mainParams.stacktrace) {
                printError(e, true);
            }
        }
        catch (IOException e) {
            printError(e, mainParams.stacktrace);
        }
    }

    private static Tuple2<String, String> decodeVersionString(final String version) {
        return Tuple2.of(SmtLibSolverManager.getSolverName(version), SmtLibSolverManager.getSolverVersion(version));
    }

    private Path createIfNotExists(final Path path) throws IOException {
        if(!Files.exists(path)) {
            Files.createDirectory(path);
        }
        return path;
    }

    private void printError(final Throwable ex, final boolean printStackTrace) {
        final String message = ex.getMessage() == null ? "" : ex.getMessage();
        logger.write(Logger.Level.RESULT, "%s occurred, message: %s%n", ex.getClass().getSimpleName(), message);
        if (printStackTrace) {
            final StringWriter errors = new StringWriter();
            ex.printStackTrace(new PrintWriter(errors));
            logger.write(Logger.Level.RESULT, "Trace:%n%s%n", errors.toString());
        }
        else {
            logger.write(Logger.Level.RESULT, "Use --stacktrace for stack trace%n");
        }
    }

    public static class SolverNameValidator implements IParameterValidator {
        @Override
        public void validate(String name, String value) throws ParameterException {
            if(!value.matches("[a-zA-Z0-9]+")) {
                throw new ParameterException(
                    String.format("Invalid solver name in parameter %s", name)
                );
            }
        }
    }

    public static class SolverNameAndVersionValidator implements IParameterValidator {
        @Override
        public void validate(String name, String value) throws ParameterException {
            final var versionArr = value.split(":");

            if(versionArr.length != 2) {
                throw new ParameterException(String.format("Invalid version string %s in parameter %s", value, name));
            }

            if(!versionArr[0].matches("[a-zA-Z0-9]+") || !versionArr[1].matches("[a-zA-Z0-9-._]+")) {
                throw new ParameterException(
                    String.format("Invalid version string %s in parameter %s", value, name)
                );
            }
        }
    }
}
