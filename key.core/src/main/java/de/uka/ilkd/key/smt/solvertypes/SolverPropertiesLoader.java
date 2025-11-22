/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.solvertypes;

import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.nparser.ParsingFacade;
import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.settings.PathConfig;
import de.uka.ilkd.key.settings.SettingsConverter;
import de.uka.ilkd.key.smt.communication.Z3Socket;
import de.uka.ilkd.key.smt.newsmt2.ModularSMTLib2Translator;

import org.key_project.util.Streams;
import org.key_project.util.reflection.ClassLoaderUtil;

import org.antlr.v4.runtime.CharStreams;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/// This class provides [SolverType] instances based on the current SMT solver definitions in
/// various configuration files.
///
/// The configuration are in loaded from
/// 1. The current working directory: `./smt-solvers.json`
/// 2. Path from system property : `-P key.smt_solvers=<path>`
/// 3. The KeY user configuration folder: `~/.key/smt-solvers.json`
/// 4. All resources with the name `de/uka/ilkd/key/smt/solvertypes/solvers.key.json` in the
/// classpath.
///
/// Local configuration overwrites user configuration overwrites classpath configuration.
/// All configuration is overwritten using the {@link ProofIndependentSettings#getSMTSettings()}.
///
/// Use (1) and (2) rather to add new SMT solvers to KeY.
///
/// @author Alicia Appelhagen
/// @author Alexander Weigl
public class SolverPropertiesLoader {
    private static final Logger LOGGER = LoggerFactory.getLogger(SolverPropertiesLoader.class);

    /// Name of the file containing the names of the SMT properties files to be loaded.
    public static final String SOLVER_LIST_FILE = "smt-solvers.json";

    /// Package path of the solvers.txt file.
    public static final String PACKAGE_PATH = "de/uka/ilkd/key/smt/solvertypes/";

    /// Java system property key denoting a path for further definitions of SMT solvers.
    public static final String SYSTEM_PROPERTY_KEY_SMT_SOLVERS = "key.smt_solvers";

    /**
     * The solvers loaded by this loader.
     */
    private static final Collection<SolverType> SOLVERS = new ArrayList<>(5);
    /**
     * The EXPERIMENTAL solvers loaded by this loader.
     */
    private static final Collection<SolverType> EXPERIMENTAL_SOLVERS = new ArrayList<>(2);

    /**
     * The default solver NAME, if none is given in the .props file.
     */
    private static final String DEFAULT_NAME = "SMT Solver";
    /**
     * The default solver COMMAND, if none is given in the .props file.
     */
    private static final String DEFAULT_COMMAND = "command";
    /**
     * The default process parameters, if none are given in the .props file.
     */
    private static final String DEFAULT_PARAMS = "-parameter";
    /**
     * The default solver description, if none is given in the .props file.
     */
    private static final String DEFAULT_INFO = "An SMT solver.";
    /**
     * The default VERSION parameter, if none is given in the .props file.
     */
    private static final String DEFAULT_VERSION = "-version";
    /**
     * The default minimal expected VERSION, if none is given in the .props file.
     */
    private static final String DEFAULT_MINIMUM_VERSION = "";
    /**
     * The default {@link de.uka.ilkd.key.smt.SMTTranslator}, if none is given in the .props file:
     * {@link ModularSMTLib2Translator}.
     */
    private static final String DEFAULT_TRANSLATOR =
        "de.uka.ilkd.key.smt.newsmt2.ModularSMTLib2Translator";
    /**
     * The default {@link de.uka.ilkd.key.smt.communication.AbstractSolverSocket}, if none is given
     * in the .props file: {@link Z3Socket}.
     */
    private static final String DEFAULT_SOLVER_SOCKET =
        "de.uka.ilkd.key.smt.communication.Z3Socket";
    /**
     * The default solver TIMEOUT, if none is given in the .props file.
     */
    private static final long DEFAULT_TIMEOUT = -1;

    /**
     * The .props key for the solver's NAME.
     */
    private static final String NAME = "name";
    /**
     * The .props key for the solver's default process COMMAND.
     */
    private static final String COMMAND = "command";
    /**
     * The .props key for the solver's default process parameters.
     */
    private static final String PARAMS = "params";
    /**
     * The .props key for the solver's VERSION parameter.
     */
    private static final String VERSION = "version";
    /**
     * The .props key for the solver's message DELIMITERS.
     */
    private static final String DELIMITERS = "delimiters";
    /**
     * The .props key for information about the solver.
     */
    private static final String INFO = "info";
    /**
     * The .props key for the solver's default TIMEOUT.
     */
    private static final String TIMEOUT = "timeout";
    /**
     * The .props key for the minimal expected solver VERSION.
     */
    private static final String MIN_VERSION = "minVersion";
    /**
     * The .props key for signalling whether the solver is an EXPERIMENTAL solver (only used in
     * experimental mode). Default value is false.
     */
    private static final String EXPERIMENTAL = "experimental";
    /**
     * The .props key for the solver's
     * {@link de.uka.ilkd.key.smt.communication.AbstractSolverSocket}. Default socket is
     * {@link Z3Socket}.
     */
    private static final String SOLVER_SOCKET_CLASS = "socketClass";
    /**
     * The .props key for the solver's {@link de.uka.ilkd.key.smt.SMTTranslator}. Default translator
     * is {@link ModularSMTLib2Translator}.
     */
    private static final String TRANSLATOR_CLASS = "translatorClass";
    /**
     * The .props key for the solver's {@link de.uka.ilkd.key.smt.newsmt2.SMTHandler}s. Default is
     * an empty list leading to all handlers being used. Only takes effect when used with
     * {@link ModularSMTLib2Translator}.
     */
    private static final String HANDLER_NAMES = "handlers";
    /**
     * The .props key for the solver's handler options (arbitrary String list).
     */
    private static final String HANDLER_OPTIONS = "handlerOptions";
    /**
     * The .props key for the path to the solver's preamble file. If this is not a valid path, the
     * default preamble will be used by making the parameter null.
     */
    private static final String PREAMBLE_FILE = "preamble";

    /**
     * All supported keys for solver props files.
     */
    private static final String[] SUPPORTED_KEYS = { NAME, VERSION, COMMAND, PARAMS, DELIMITERS,
        INFO, MIN_VERSION, EXPERIMENTAL, TIMEOUT, SOLVER_SOCKET_CLASS, TRANSLATOR_CLASS,
        HANDLER_NAMES, HANDLER_OPTIONS, PREAMBLE_FILE };

    /**
     * If a props file does not contain a solver NAME or two files have the same NAME, unique names
     * have to be created because interacting with the solvers later requires uniqueness. The
     * counters are used for uniqueness across the solvers of this loader.
     */
    private static final Map<String, Integer> NAME_COUNTERS = new HashMap<>();

    private static String uniqueName(String name) {
        Integer counter = NAME_COUNTERS.get(name);
        // if NAME has not been used yet, use it and set counter to 0
        if (counter == null) {
            NAME_COUNTERS.put(name, 0);
            return name;
        }
        // if NAME was already used, use <NAME>_<counter> as NAME and increase counter afterwards
        String nameBuilder = name +
            "_" +
            counter;
        counter++;
        NAME_COUNTERS.put(name, counter);
        // <NAME>_<counter> is now also a NAME that has been used and must be unique
        return uniqueName(nameBuilder);
    }

    /**
     * Initializes {@link #SOLVERS} using the given hardcoded properties if that list is empty,
     * otherwise just returns the existing list.
     * The solver type names are unique across the returned list.
     * Note that care may have to be taken for the names to be globally unique
     * (see {@link SolverTypes}).
     *
     * @return a copy of the created list of solver types
     */
    public Collection<SolverType> getSolvers() {
        if (SOLVERS.isEmpty()) {
            for (Configuration solverProp : loadSolvers().getSections()) {
                SolverType createdType = makeSolver(solverProp);
                SOLVERS.add(createdType);
                /*
                 * If the solver is an EXPERIMENTAL solver (only available in experimental mode),
                 * add it to the separate list:
                 */
                if (solverProp.getBool(EXPERIMENTAL, false)) {
                    EXPERIMENTAL_SOLVERS.add(createdType);
                }
            }
        }
        return new ArrayList<>(SOLVERS);
    }

    /**
     * @return a copy of the created list of experimental solvers
     */
    public Collection<SolverType> getExperimentalSolvers() {
        getSolvers();
        return new ArrayList<>(EXPERIMENTAL_SOLVERS);
    }

    /**
     * Create a {@link SolverTypeImplementation} from a Properties object.
     */
    private static SolverType makeSolver(Configuration props) {
        String preamble = null;
        Class<?> solverSocketClass;
        Class<?> translatorClass;

        // Read props file to create a SolverTypeImplementation object:

        // the solver's NAME has to be unique
        String name = uniqueName(props.getString(NAME, DEFAULT_NAME));

        // default solver COMMAND, TIMEOUT, parameters, VERSION parameter, solver INFO (some string)
        String command = props.getString(COMMAND, DEFAULT_COMMAND);
        long timeout = Math.max(-1, props.getLong(TIMEOUT, DEFAULT_TIMEOUT));

        String params = props.getString(PARAMS, DEFAULT_PARAMS);
        String version = props.getString(VERSION, DEFAULT_VERSION);
        String minVersion = props.getString(MIN_VERSION, DEFAULT_MINIMUM_VERSION);
        String info = props.getString(INFO, DEFAULT_INFO);

        // the solver socket used for communication with the created solver
        String socketClassName = props.getString(SOLVER_SOCKET_CLASS, DEFAULT_SOLVER_SOCKET);
        try {
            solverSocketClass = ClassLoaderUtil.getClassforName(socketClassName);
        } catch (ClassNotFoundException e) {
            LOGGER.error("Could not find solver socket class {}. Fallback to Z3Socket.class ",
                socketClassName, e);
            solverSocketClass = Z3Socket.class;
        }


        // the message DELIMITERS used by the created solver in its stdout
        String[] delimiters =
            props.getStringArray(SolverPropertiesLoader.DELIMITERS, new String[] { "\n", "\r" });

        // the smt translator (class SMTTranslator) used by the created solver
        String translatorClassName = props.getString(TRANSLATOR_CLASS, DEFAULT_TRANSLATOR);
        try {
            translatorClass = ClassLoaderUtil.getClassforName(translatorClassName);
        } catch (ClassNotFoundException e) {
            LOGGER.error(
                "Could not find translator class {}; using ModularSMTLib2Translator.class.",
                translatorClassName, e);
            translatorClass = ModularSMTLib2Translator.class;
        }

        // the SMTHandlers used by the created solver
        // note that this will only take effect when using ModularSMTLib2Translator ...
        String[] handlerNames = props.getStringArray(HANDLER_NAMES, new String[0]);
        String[] handlerOptions = props.getStringArray(HANDLER_OPTIONS, new String[0]);

        // the solver specific preamble, may be null
        String preambleFile = props.getString(PREAMBLE_FILE);
        if (preambleFile != null) {
            var loader = SolverPropertiesLoader.class.getClassLoader();
            InputStream fileContent = loader.getResourceAsStream(preambleFile);
            if (fileContent != null) {
                try {
                    preamble = Streams.toString(fileContent);
                } catch (IOException ignored) {
                }
            }
        }

        // create the solver type
        return new SolverTypeImplementation(name, info, params, command, version, minVersion,
            timeout, delimiters, translatorClass, handlerNames, handlerOptions, solverSocketClass,
            preamble);
    }

    /**
     * Loads the solvers that are specified in .props files in resource packages named
     * "de/uka/ilkd/key/smt/solvertypes".
     */
    static Configuration loadSolvers() {
        try { // load single solvers.txt files from the same location everywhere in the classpath
            var filesInClasspath =
                Streams.fromEnumerator(SolverPropertiesLoader.class.getClassLoader()
                        .getResources(PACKAGE_PATH + SOLVER_LIST_FILE)).toList();
            var solverFiles = new ArrayList<>(filesInClasspath);

            Path user = getUserSmtSolverPath();
            if (Files.exists(user)) {
                LOGGER.info("Loading a SMT solver definitions from {}", user);
                solverFiles.add(user.toUri().toURL());
            }

            Path sysProp = getSystemPropertySmtSolverPath();
            if (sysProp != null && Files.exists(sysProp)) {
                LOGGER.info("Loading a SMT solver definitions from {}", sysProp);
                solverFiles.add(sysProp.toUri().toURL());
            }

            Path local = getLocalSmtSolverPath();
            if (Files.exists(user)) {
                LOGGER.info("Loading a SMT solver definitions from {}", local);
                solverFiles.add(local.toUri().toURL());
            }

            final Configuration solverConfiguration = new Configuration();

            for (var res : solverFiles) {
                try (InputStream stream = res.openStream()) {
                    var config = ParsingFacade.readConfigurationFile(
                        CharStreams.fromStream(stream, StandardCharsets.UTF_8));

                    // Create a warning if unsupported keys occur in the loaded file.
                    Collection<String> unsupportedKeys = SettingsConverter
                            .unsupportedPropertiesKeysInSubSections(config, SUPPORTED_KEYS);
                    if (!unsupportedKeys.isEmpty()) {
                        LOGGER.warn("File {} contains unsupported keys: {}", res, unsupportedKeys);
                    }

                    solverConfiguration.overwriteWith(config);
                } catch (IOException ex) {
                    throw new RuntimeException(ex);
                }
            }
            return solverConfiguration;
        } catch (IOException e) {
            throw new RuntimeException("Could not load " + PACKAGE_PATH + SOLVER_LIST_FILE, e);
        }
    }


    /// Path for local smt solver definitions. Precedence over user and classpath smt solver
    /// configs.
    public static Path getLocalSmtSolverPath() {
        return Paths.get(SOLVER_LIST_FILE);
    }


    /// Path for user-wide smt solver definitions. Precedence over classpath smt solver configs,
    /// overwritten by local configs.
    public static Path getUserSmtSolverPath() {
        return PathConfig.getKeyConfigDir().resolve(SOLVER_LIST_FILE);
    }


    /// Path for smt solver definitions given per Java system properties.
    public static @Nullable Path getSystemPropertySmtSolverPath() {
        var path = System.getProperty(SYSTEM_PROPERTY_KEY_SMT_SOLVERS);
        if (path != null) {
            return Paths.get(path);
        }
        return null;
    }
}
