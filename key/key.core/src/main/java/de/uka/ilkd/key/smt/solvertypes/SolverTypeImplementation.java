package de.uka.ilkd.key.smt.solvertypes;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.smt.*;
import de.uka.ilkd.key.smt.communication.AbstractSolverSocket;
import de.uka.ilkd.key.smt.communication.Z3Socket;
import de.uka.ilkd.key.smt.newsmt2.ModularSMTLib2Translator;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.io.File;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.util.Arrays;

/**
 * Final SolverType implementation that uses building blocks for the various methods.
 * This can be used to modify a ModifiableSolverType object using .props files only,
 * for example (see {@link SolverPropertiesLoader}).
 *
 * The building blocks that can be modified on creation are:
 * - The various String parameters such as default command, params and the name
 * - The solver type's default timeout
 * - The message delimiters used by solver processes of the created solver type
 * - The {@link AbstractSolverSocket} used to interpret messages by solver processes of the
 *      created type
 * - The {@link SMTTranslator} used to translate messages for processes of the created solver type
 * - The {@link de.uka.ilkd.key.smt.newsmt2.SMTHandler}s used by the translator
 *      (if {@link ModularSMTLib2Translator} is used)
 * - The preamble file used for translations for the solver type
 *
 * @author alicia
 */
public final class SolverTypeImplementation implements SolverType {

    private static final Logger LOGGER = LoggerFactory.getLogger(SolverTypeImplementation.class);

    /**
     * The default values of this solver type object, final and private as they should not be
     * changed after creation.
     */
    private final String name;
    private final String info;
    private final String defaultParams;
    private final String defaultCommand;
    private final String versionCommand;
    private final String minimumSupportedVersion;
    private final long defaultTimeout;
    private final String[] delimiters;
    /**
     * The current command line parameters, timeout and command to be used instead of the default
     * values, changeable.
     */
    private String params;
    private String command;
    private long timeout;
    /**
     * Booleans signalling whether the support/installation of the
     * created solver type as an actual program has been checked.
     */
    private boolean supportHasBeenChecked = false;
    private boolean isSupportedVersion = false;
    private boolean installWasChecked = false;
    private boolean isInstalled = false;
    /**
     * The versionCommand of the solver type at hand, returned by the actual program using the
     * {@link #versionCommand} cmd parameter.
     */
    private String installedVersion;
    /**
     * The names of the {@link de.uka.ilkd.key.smt.newsmt2.SMTHandler}s to be used by the
     * {@link SMTTranslator} that is created with {@link #createTranslator(Services)}.
     */
    private final String[] handlerNames;
    private final String[] handlerOptions;
    /**
     * The class of the {@link de.uka.ilkd.key.smt.communication.AbstractSolverSocket}
     * to be created with {@link #getSocket(ModelExtractor)}.
     */
    private final Class<?> solverSocketClass;
    /**
     * The class of the {@link SMTTranslator} to be created with
     * {@link #createTranslator(Services)}.
     */
    private final Class<?> translatorClass;
    /**
     * The preamble String for the created {@link SMTTranslator}, may be null.
     */
    @Nullable
    private final String preamble;

    private final SMTTranslator translator;

    /**
     * Instantiate the solver type object with all its default values.
     * The changeable values such as {@link #command} and {@link #params}
     * are initially the same as their default values.
     * @param name the name, e.g. "Z3"
     * @param info some information about the solver type
     * @param defaultParams the default command line PARAMETERS used to start the actual solver
     *                      program
     * @param defaultCommand the default command line COMMAND used to start the actual solver
     *                       program
     * @param versionCommand the command line parameter used to get the versionCommand of the
     *                       actual solver program
     * @param minimumSupportedVersion the minimum supported versionCommand of the solver type
     *                                at hand
     * @param defaultTimeout the default solver timeout for SMT processes using this solver type
     * @param delimiters the message delimiters used by the actual solver program
     * @param translatorClass the {@link SMTTranslator} class used by this solver type
     * @param handlerNames the names of the {@link de.uka.ilkd.key.smt.newsmt2.SMTHandler}s to
     *                     be used by the {@link SMTTranslator} created by this solver type
     * @param handlerOptions arbitrary String options used by the SMTHandlers
     * @param solverSocketClass the {@link de.uka.ilkd.key.smt.communication.AbstractSolverSocket}
     *                          class used by the solver type at hand
     * @param preamble the preamble String for the created {@link SMTTranslator}, may be null
     */
    public SolverTypeImplementation(String name, String info, String defaultParams,
                                    String defaultCommand, String versionCommand,
                                    String minimumSupportedVersion,
                                    long defaultTimeout, String[] delimiters,
                                    Class<?> translatorClass,
                                    String[] handlerNames, String[] handlerOptions,
                                    Class<?> solverSocketClass, String preamble) {
        this.name = name;
        this.info = info;
        this.defaultParams = defaultParams;
        params = defaultParams;
        this.defaultCommand = defaultCommand;
        command = defaultCommand;
        this.defaultTimeout = defaultTimeout;
        this.minimumSupportedVersion = minimumSupportedVersion;
        timeout = defaultTimeout;
        this.delimiters = delimiters;
        this.versionCommand = versionCommand;
        this.translatorClass = translatorClass;
        // copy the array so that it cannot accidentally be manipulated from the outside
        this.handlerNames = Arrays.copyOf(handlerNames, handlerNames.length);
        this.handlerOptions = Arrays.copyOf(handlerOptions, handlerOptions.length);
        this.solverSocketClass = solverSocketClass;
        this.preamble = preamble;
        this.translator = makeTranslator();
    }

    private SMTTranslator makeTranslator() {
        try {
            return (SMTTranslator) translatorClass
                    .getDeclaredConstructor(String[].class, String[].class, String.class)
                    .newInstance(handlerNames, handlerOptions, preamble);
        } catch (NoSuchMethodException | IllegalArgumentException | ClassCastException
                | InstantiationException | IllegalAccessException | InvocationTargetException e) {
            LOGGER.warn(String.format(
                    "Using default ModularSMTLib2Translator for SMT translation due to" +
                            " exception: %n %s", e.getMessage()));
            return new ModularSMTLib2Translator();
        }
    }

    /**
     * Returns false whenever cmd is null or empty, otherwise the environment variables are
     * checked for the command and if no file with the command's name is found in any of those
     * paths, the cmd itself is used as the pathname.
     * If all of these fail, the cmd is also not installed.
     * @param cmd the command
     * @return true iff the command is a non-empty String and a file with the command's name or with
     *          the command as pathname can be found in the file system.
     */
    public static boolean isInstalled(@Nullable String cmd) {
        if (cmd == null || cmd.isEmpty()) {
            return false;
        }
        if (checkEnvVariable(cmd)) {
            return true;
        } else {
            File file = new File(cmd);
            return file.exists() && !file.isDirectory();
        }
    }

    private static boolean checkEnvVariable(@Nullable String cmd) {
        String path = System.getenv("PATH");
        String[] res = path.split(File.pathSeparator);
        for (String s : res) {
            // for empty cmd, this file will always exist
            File file = new File(s + File.separator + cmd);
            if (file.exists()) {
                return true;
            }
        }
        return false;
    }

    @Override
    public SMTSolver createSolver(SMTProblem problem, SolverListener listener, Services services) {
        return new SMTSolverImplementation(problem, listener, services, this);
    }

    @Override
    public String getName() {
        return name;
    }

    @Override
    public boolean isInstalled(boolean recheck) {
        if (recheck || !installWasChecked) {

            String cmd = getSolverCommand();

            isInstalled = isInstalled(cmd);
            if (isInstalled) {
                installWasChecked = true;
            }

        }
        return isInstalled;
    }

    @Override
    public String getInfo() {
        return info;
    }

    @Override
    public String getSolverParameters() {
        return params;
    }

    @Override
    public void setSolverParameters(String s) {
        params = s;
    }

    @Override
    public String getDefaultSolverParameters() {
        return defaultParams;
    }

    @Override
    public String getSolverCommand() {
        return command;
    }

    @Override
    public void setSolverCommand(String s) {
        command = s;
    }

    @Override
    public String getDefaultSolverCommand() {
        return defaultCommand;
    }

    @Override
    public long getSolverTimeout() {
        return timeout;
    }

    @Override
    public void setSolverTimeout(long timeout) {
        this.timeout = timeout;
    }

    @Override
    public long getDefaultSolverTimeout() {
        return defaultTimeout;
    }

    @Override
    public SMTTranslator createTranslator() {
        return translator;
    }

    @Override
    public String[] getDelimiters() {
        // Copy the delimiters array so that it cannot accidentally be manipulated from the outside.
        return Arrays.copyOf(delimiters, delimiters.length);
    }

    // TODO Make this modifiable?
    @Override
    public String modifyProblem(String problem) {
        return problem;
    }

    @Override
    public String getVersionParameter() {
        return versionCommand;
    }

    @Override
    public String getMinimumSupportedVersion() {
        return minimumSupportedVersion;
    }

    @Override
    public String getInstalledVersion() {
        return installedVersion;
    }

    @Override
    public @Nullable String getRawVersion() {
        // Don't let the version String be empty because that will lead to the solver run
        if (isInstalled(true)) {
            String version = VersionChecker.INSTANCE.getVersionFor(getSolverCommand(),
                    getVersionParameter());
            if (version == null) {
                version = "unknown version";
            }
            return version;
        } else {
            return null;
        }
    }

    @Override
    public boolean isSupportedVersion() {
        if (!supportHasBeenChecked) {
            checkForSupport();
        }
        return isSupportedVersion;
    }

    /**
     * Note that the actual version is only compared to the minimum version lexicographically.
     * This is a temporary solution as it may lead to weird behaviour, for example shorter
     * Strings will be before longer Strings and 1.14.1 will be before 1.8.10 even though they have the same length.
     *
     * If that lexicographical comparison is not possible, you may have to
     * modify the SolverTypeImplementation class and change SolverPropertiesLoader accordingly.
     *
     * TODO Find better solution
     */
    @Override
    public boolean checkForSupport() {
        if (!isInstalled) {
            return false;
        }
        supportHasBeenChecked = true;
        installedVersion = getRawVersion();
        if (installedVersion == null) {
            installedVersion = "";
            isSupportedVersion = false;
            return false;
        }
        isSupportedVersion = installedVersion.compareTo(getMinimumSupportedVersion()) >= 0;
        return isSupportedVersion;
    }

    @Override
    public boolean supportHasBeenChecked() {
        return supportHasBeenChecked;
    }

    @Nonnull
    @Override
    public AbstractSolverSocket getSocket(ModelExtractor query) {
        try {
            return (AbstractSolverSocket) solverSocketClass
                    .getDeclaredConstructor(String.class, ModelExtractor.class)
                    .newInstance(name, query);
        } catch (NoSuchMethodException | IllegalArgumentException | ClassCastException
                | InstantiationException | IllegalAccessException | InvocationTargetException e) {
            LOGGER.warn(
                    "Using default Z3Socket for solver communication due to exception:"
                            + System.lineSeparator()
                            + e.getMessage());
            return new Z3Socket(name, query);
        }
    }

}
