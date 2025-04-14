/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.solvertypes;

import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.nparser.ParsingFacade;
import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.settings.SettingsConverter;
import de.uka.ilkd.key.smt.communication.Z3Socket;
import de.uka.ilkd.key.smt.newsmt2.ModularSMTLib2Translator;

import org.key_project.util.Streams;
import org.key_project.util.reflection.ClassLoaderUtil;

import org.antlr.v4.runtime.CharStreams;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Provides static SolverType objects to be reused and saves the properties to .props files. Used to
 * create {@link SolverType} (in the form of {@link SolverTypeImplementation}) objects from .props
 * files.
 *
 * @author Alicia Appelhagen
 */
public class SolverPropertiesLoader {

    /**
     * Logger.
     */
    private static final Logger LOGGER = LoggerFactory.getLogger(SolverPropertiesLoader.class);

    /**
     * Name of the file containing the names of the SMT properties files to be loaded.
     */
    private static final String SOLVER_LIST_FILE = "solvers.key.json";
    /**
     * Package path of the solvers.txt file.
     */
    private static final String PACKAGE_PATH = "de/uka/ilkd/key/smt/solvertypes/";

    /**
     * The solvers loaded by this loader.
     */
    private static final Collection<SolverType> SOLVERS = new ArrayList<>(5);
    /**
     * The LEGACY solvers loaded by this loader.
     */
    private static final Collection<SolverType> LEGACY_SOLVERS = new ArrayList<>(2);

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
     * in the .props file: {@link de.uka.ilkd.key.smt.communication.Z3Socket}.
     */
    private static final String DEFAULT_SOLVER_SOCKET =
        "de.uka.ilkd.key.smt.communication.Z3Socket";
    /**
     * The default message DELIMITERS, if none are given in the .props file.
     */
    private static final String[] DEFAULT_DELIMITERS = new String[] { "\n", "\r" };
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
     * The .props key for signalling whether the solver is a LEGACY solver (only used in
     * experimental mode). Default value is false.
     */
    private static final String LEGACY = "legacy";
    /**
     * The .props key for the solver's
     * {@link de.uka.ilkd.key.smt.communication.AbstractSolverSocket}. Default socket is
     * {@link de.uka.ilkd.key.smt.communication.Z3Socket}.
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
        INFO, MIN_VERSION, LEGACY, TIMEOUT, SOLVER_SOCKET_CLASS, TRANSLATOR_CLASS,
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
                // If the solver is a LEGACY solver (only available in experimental mode),
                // add it to the separate list:
                if (solverProp.getBool(LEGACY, false)) {
                    LEGACY_SOLVERS.add(createdType);
                }
            }
        }
        return new ArrayList<>(SOLVERS);
    }

    /**
     * @return a copy of the created list of legacy solvers
     */
    public Collection<SolverType> getLegacySolvers() {
        getSolvers();
        return new ArrayList<>(LEGACY_SOLVERS);
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
        String name = uniqueName(props.getString(SolverPropertiesLoader.NAME, DEFAULT_NAME));

        // default solver COMMAND, TIMEOUT, parameters, VERSION parameter, solver INFO (some string)
        String command = props.getString(SolverPropertiesLoader.COMMAND, DEFAULT_COMMAND);
        long timeout = Math.max(-1, props.getLong(SolverPropertiesLoader.TIMEOUT, DEFAULT_TIMEOUT));

        String params = props.getString(SolverPropertiesLoader.PARAMS, DEFAULT_PARAMS);
        String version = props.getString(SolverPropertiesLoader.VERSION, DEFAULT_VERSION);
        String minVersion =
            props.getString(SolverPropertiesLoader.MIN_VERSION, DEFAULT_MINIMUM_VERSION);
        String info = props.getString(SolverPropertiesLoader.INFO, DEFAULT_INFO);

        // the solver socket used for communication with the created solver
        String socketClassName = props.getString(SOLVER_SOCKET_CLASS, DEFAULT_SOLVER_SOCKET);
        try {
            solverSocketClass = ClassLoaderUtil.getClassforName(socketClassName);
        } catch (ClassNotFoundException e) {
            LOGGER.error("Could not find solver socket class {}", socketClassName, e);
            solverSocketClass = Z3Socket.class;
        }


        // the message DELIMITERS used by the created solver in its stdout
        String[] delimiters =
            props.getStringArray(SolverPropertiesLoader.DELIMITERS, new String[0]);

        // the smt translator (class SMTTranslator) used by the created solver
        String translatorClassName = props.getString(TRANSLATOR_CLASS, DEFAULT_TRANSLATOR);
        try {
            translatorClass = ClassLoaderUtil.getClassforName(translatorClassName);
        } catch (ClassNotFoundException e) {
            LOGGER.error("Could not find translator class {}", translatorClassName, e);
            translatorClass = ModularSMTLib2Translator.class;
        }

        // the SMTHandlers used by the created solver
        // note that this will only take effect when using ModularSMTLib2Translator ...
        String[] handlerNames =
            props.getStringArray(SolverPropertiesLoader.HANDLER_NAMES, new String[0]);
        String[] handlerOptions =
            props.getStringArray(SolverPropertiesLoader.HANDLER_OPTIONS, new String[0]);

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
    private static Configuration loadSolvers() {
        try { // load single solvers.txt files from the same location everywhere in the classpath
            final var solverTxts =
                Streams.fromEnumerator(SolverPropertiesLoader.class.getClassLoader()
                        .getResources(PACKAGE_PATH + SOLVER_LIST_FILE)).toList();

            final Configuration solverConfiguration = new Configuration();

            for (var res : solverTxts) {
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
}
