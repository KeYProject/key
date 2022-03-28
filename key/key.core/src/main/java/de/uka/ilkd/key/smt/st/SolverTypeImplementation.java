package de.uka.ilkd.key.smt.st;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.smt.*;
import de.uka.ilkd.key.smt.communication.SolverSocket;
import de.uka.ilkd.key.smt.newsmt2.ModularSMTLib2Translator;

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
 * <p>
 * The building blocks that can be modified on creation are:
 * - The various String parameters such as default command, params and the name
 * - The solver type's default timeout
 * - The message delimiters used by solver processes of the created solver type
 * - The {@link SolverSocket.MessageHandler} used to interpret messages by solver processes of the
 *      created type
 * - The {@link SMTTranslator} used to translate messages for processes of the created solver type
 * - The {@link de.uka.ilkd.key.smt.newsmt2.SMTHandler}s used by the translator
 *      (if {@link ModularSMTLib2Translator} is used)
 * - The preamble file used for translations for the solver type
 *
 * @author alicia
 */
public final class SolverTypeImplementation implements SolverType {

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
     * The {@link SolverSocket.MessageHandler} used by
     * the {@link SolverSocket} created with {@link #getSocket(ModelExtractor)}.
     */
    private final SolverSocket.MessageHandler msgHandler;
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
     * @param messageHandler the {@link SolverSocket.MessageHandler}
     *                         used by the solver type at hand
     * @param preamble the preamble String for the created {@link SMTTranslator}, may be null
     */
    public SolverTypeImplementation(String name, String info, String defaultParams,
                                    String defaultCommand, String versionCommand,
                                    String minimumSupportedVersion,
                                    long defaultTimeout, String[] delimiters,
                                    Class<?> translatorClass,
                                    String[] handlerNames, String[] handlerOptions,
                                    SolverSocket.MessageHandler messageHandler, String preamble) {
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
        msgHandler = messageHandler;
        this.preamble = preamble;
    }

    public static boolean isInstalled(String cmd) {
        if (checkEnvVariable(cmd)) {
            return true;
        } else {
            File file = new File(cmd);
            return file.exists() && !file.isDirectory();
        }
    }

    private static boolean checkEnvVariable(String cmd) {
        String path = System.getenv("PATH");
        String[] res = path.split(File.pathSeparator);
        for (String s : res) {
            File file = new File(s + File.separator + cmd);
            if (file.exists()) {
                return true;
            }
        }
        return false;
    }

    @Override
    public SMTSolver createSolver(SMTProblem problem, SolverListener listener, Services services) {
        // TODO Make this modifiable? (similar to SMTTranslator)
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

    // TODO services is never used
    @Override
    public SMTTranslator createTranslator(Services services) {
        Constructor<?>[] constructors = translatorClass.getConstructors();
        SMTTranslator smtTranslator = null;
        boolean instantiated = false;
        for (int i = 0; i < constructors.length; i++) {
            try {
                smtTranslator = (SMTTranslator) constructors[i]
                        .newInstance(handlerNames, handlerOptions, preamble);
                instantiated = true;
                break;
            } catch (IllegalArgumentException | ClassCastException | InstantiationException
                    | IllegalAccessException | InvocationTargetException e) {
                instantiated = false;
            }
        }
        // default fallback option
        if (!instantiated) {
            return new ModularSMTLib2Translator();
        }
        return smtTranslator;
    }

    @Override
    public String[] getDelimiters() {
        // Copy the delimiters array so that it cannot accidentally be manipulated from the outside.
        return Arrays.copyOf(delimiters, delimiters.length);
    }

    // TODO How to make this modifiable?
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

    // TODO Fuse this with getVersion()
    @Override
    public String getRawVersion() {
        if (isInstalled(true)) {
            return VersionChecker.INSTANCE.getVersionFor(getSolverCommand(), getVersionParameter());
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
    public SolverSocket getSocket(ModelExtractor query) {
        return new SolverSocket(name, query, msgHandler);
    }

}
