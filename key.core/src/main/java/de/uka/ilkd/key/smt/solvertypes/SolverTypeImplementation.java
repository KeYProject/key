/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.solvertypes;

import java.io.File;
import java.lang.reflect.InvocationTargetException;
import java.nio.file.Paths;
import java.util.Arrays;
import javax.annotation.Nonnull;
import javax.annotation.Nullable;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.smt.*;
import de.uka.ilkd.key.smt.communication.AbstractSolverSocket;
import de.uka.ilkd.key.smt.communication.Z3Socket;
import de.uka.ilkd.key.smt.newsmt2.ModularSMTLib2Translator;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Final SolverType implementation that uses building blocks for the various methods. This can be
 * used to modify a ModifiableSolverType object using .props files only, for example (see
 * {@link SolverPropertiesLoader}).
 *
 * The building blocks that can be modified on creation are: - The various String parameters such as
 * default command, params and the name - The solver type's default timeout - The message delimiters
 * used by solver processes of the created solver type - The {@link AbstractSolverSocket} used to
 * interpret messages by solver processes of the created type - The {@link SMTTranslator} used to
 * translate messages for processes of the created solver type - The
 * {@link de.uka.ilkd.key.smt.newsmt2.SMTHandler}s used by the translator (if
 * {@link ModularSMTLib2Translator} is used) - The preamble file used for translations for the
 * solver type
 *
 * @author Alicia Appelhagen
 */
public final class SolverTypeImplementation implements SolverType {

    private static final Logger LOGGER = LoggerFactory.getLogger(SolverTypeImplementation.class);

    /*
     * The default values of this solver type object, final and private as they should not be
     * changed after creation.
     */

    /**
     * The name of this solver type.
     */
    private final String name;

    /**
     * Arbitrary information for this solver type, shown in the type's settings dialog.
     */
    private final String info;

    /**
     * The default parameters for starting a solver process with this solver type.
     */
    private final String defaultParams;

    /**
     * The default command for starting a solver process with this solver type.
     */
    private final String defaultCommand;

    /**
     * The parameter used to get the version of a solver of this type.
     */
    private final String versionParameter;

    /**
     * The minimum version a solver of this type needs to have to be declared as supported by KeY.
     */
    private final String minimumSupportedVersion;

    /**
     * The default timeout for solver processes of this type.
     */
    private final long defaultTimeout;

    /**
     * The message delimiters used to separate messages in the stdout of processes of this type.
     */
    private final String[] delimiters;

    /*
     * The current command line parameters, timeout and command to be used instead of the default
     * values, changeable.
     */

    /**
     * The current parameters for starting processes of this type.
     */
    private String params;

    /**
     * The current command for starting processes of this type.
     */
    private String command;

    /**
     * The current timeout of processes of this type.
     */
    private long timeout;

    /*
     * Booleans signalling whether the support/installation of the created solver type as an actual
     * program has been checked.
     */

    /**
     * Has the support of the solver version of solvers(/solver processes) of this type already been
     * checked?
     */
    private boolean supportHasBeenChecked = false;

    /**
     * Is the version of solvers(/solver processes) of this type supported?
     */
    private boolean isSupportedVersion = false;

    /**
     * Has this solver type already been checked for installation?
     */
    private boolean installWasChecked = false;

    /**
     * True iff the current command is a file.
     */
    private boolean isInstalled = false;

    /**
     * The versionParameter of the solver type at hand, returned by the actual program using the
     * {@link #versionParameter} cmd parameter.
     */
    private String installedVersion;

    /**
     * The names of the {@link de.uka.ilkd.key.smt.newsmt2.SMTHandler}s to be used by the
     * {@link SMTTranslator} that is created with {@link #createTranslator()}.
     */
    private final String[] handlerNames;

    /**
     * Arbitrary options for the {@link de.uka.ilkd.key.smt.newsmt2.SMTHandler}s used by this solver
     * type's {@link #translator} (only takes effect for {@link ModularSMTLib2Translator}).
     */
    private final String[] handlerOptions;

    /**
     * The class of the {@link de.uka.ilkd.key.smt.communication.AbstractSolverSocket} to be created
     * with {@link #getSocket(ModelExtractor)}.
     */
    private final Class<?> solverSocketClass;

    /**
     * The class of the {@link SMTTranslator} to be created with {@link #createTranslator()}.
     */
    private final Class<?> translatorClass;

    /**
     * The preamble String for the created {@link SMTTranslator}, may be null.
     */
    @Nullable
    private final String preamble;

    /**
     * Used for creation of new sockets as well as modifying problem Strings. Should not be returned
     * to outside classes.
     */
    private final AbstractSolverSocket solverSocket;

    /**
     * The SMTTranslator used to translate problems for this solver type.
     */
    private final SMTTranslator translator;

    /**
     * Instantiate the solver type object with all its default values. The changeable values such as
     * {@link #command} and {@link #params} are initially the same as their default values.
     *
     * @param name the name, e.g. "Z3"
     * @param info some information about the solver type
     * @param defaultParams the default command line PARAMETERS used to start the actual solver
     *        program
     * @param defaultCommand the default command line COMMAND used to start the actual solver
     *        program
     * @param versionParameter the command line parameter used to get the versionParameter of the
     *        actual solver program
     * @param minimumSupportedVersion the minimum supported versionParameter of the solver type at
     *        hand
     * @param defaultTimeout the default solver timeout for SMT processes using this solver type
     * @param delimiters the message delimiters used by the actual solver program
     * @param translatorClass the {@link SMTTranslator} class used by this solver type
     * @param handlerNames the names of the {@link de.uka.ilkd.key.smt.newsmt2.SMTHandler}s to be
     *        used by the {@link SMTTranslator} created by this solver type
     * @param handlerOptions arbitrary String options used by the SMTHandlers
     * @param solverSocketClass the {@link de.uka.ilkd.key.smt.communication.AbstractSolverSocket}
     *        class used by the solver type at hand
     * @param preamble the preamble String for the created {@link SMTTranslator}, may be null
     */
    public SolverTypeImplementation(String name, String info, String defaultParams,
            String defaultCommand, String versionParameter, String minimumSupportedVersion,
            long defaultTimeout, String[] delimiters, Class<?> translatorClass,
            String[] handlerNames, String[] handlerOptions, Class<?> solverSocketClass,
            String preamble) {
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
        this.versionParameter = versionParameter;
        this.translatorClass = translatorClass;
        // copy the array so that it cannot accidentally be manipulated from the outside
        this.handlerNames = Arrays.copyOf(handlerNames, handlerNames.length);
        this.handlerOptions = Arrays.copyOf(handlerOptions, handlerOptions.length);
        this.solverSocketClass = solverSocketClass;
        this.preamble = preamble;
        this.translator = makeTranslator();
        this.solverSocket = makeSocket();
    }

    private AbstractSolverSocket makeSocket() {
        try {
            return (AbstractSolverSocket) solverSocketClass
                    .getDeclaredConstructor(String.class, ModelExtractor.class)
                    .newInstance(name, null);
        } catch (NoSuchMethodException | IllegalArgumentException | ClassCastException
                | InstantiationException | IllegalAccessException | InvocationTargetException e) {
            LOGGER.warn(String.format(
                "Using default Z3Socket for solver communication due to exception:%s%s",
                System.lineSeparator(), e.getMessage()));
            return new Z3Socket(name, null);
        }
    }

    private SMTTranslator makeTranslator() {
        try {
            return (SMTTranslator) translatorClass
                    .getDeclaredConstructor(String[].class, String[].class, String.class)
                    .newInstance(handlerNames, handlerOptions, preamble);
        } catch (NoSuchMethodException | IllegalArgumentException | ClassCastException
                | InstantiationException | IllegalAccessException | InvocationTargetException e) {
            LOGGER.warn(
                String.format("Using default ModularSMTLib2Translator for SMT translation due to"
                    + " exception: %n %s", e.getMessage()));
            return new ModularSMTLib2Translator();
        }
    }

    /**
     * Returns false whenever cmd is null or empty, otherwise the environment variables are checked
     * for the command and if no file with the command's name is found in any of those paths, the
     * cmd itself is used as the pathname. If all of these fail, the cmd is also not installed.
     *
     * @param cmd the command whose existence will be checked
     * @return true iff the command is a non-empty String and a file with the command's name or with
     *         the command as pathname can be found in the file system.
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

    private static boolean checkFile(String parent, String child) {
        File file = Paths.get(parent, child).toFile();
        return file.exists() && file.canExecute();
    }

    private static boolean checkEnvVariable(String cmd) {
        String pathExt = System.getenv("PATHEXT");

        // Build all possible children exes (add extensions)
        String[] exes;
        if (pathExt == null) {
            // No PATHEXT, just use cmd
            exes = new String[] { cmd };
        } else {
            String[] pathExtensions = pathExt.split(File.pathSeparator);
            exes = new String[pathExtensions.length + 1];

            // Append all extensions to cmd
            for (int i = 0; i < pathExtensions.length; i++) {
                exes[i] = cmd + pathExtensions[i];
            }
            // Add unchanged cmd to be sure (e.g. cmd = bla.exe)
            exes[pathExtensions.length] = cmd;
        }

        String path = System.getenv("PATH");
        String[] paths = path.split(File.pathSeparator);
        for (String parent : paths) {
            for (String children : exes) {
                if (checkFile(parent, children)) {
                    return true;
                }
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

    @Override
    public String modifyProblem(String problem) {
        return solverSocket.modifyProblem(problem);
    }

    @Override
    public String getVersionParameter() {
        return versionParameter;
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
            String version =
                VersionChecker.INSTANCE.getVersionFor(getSolverCommand(), getVersionParameter());
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
     * Note that the actual version is only compared to the minimum version lexicographically. This
     * is a temporary solution as it may lead to weird behaviour, for example shorter Strings will
     * be before longer Strings and 1.14.1 will be before 1.8.10 even though they have the same
     * length.
     *
     * If that lexicographical comparison is not possible, you may have to modify the
     * SolverTypeImplementation class and change SolverPropertiesLoader accordingly.
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
        AbstractSolverSocket socket = solverSocket.copy();
        socket.setQuery(query);
        return socket;
    }

}
