package de.uka.ilkd.key.smt.solvertypes;

import de.uka.ilkd.key.settings.SettingsConverter;
import de.uka.ilkd.key.smt.communication.Z3Socket;
import de.uka.ilkd.key.smt.newsmt2.ModularSMTLib2Translator;
import org.key_project.util.reflection.ClassLoaderUtil;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.net.URL;
import java.util.*;
import java.util.stream.Collectors;

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
    private static final String SOLVER_LIST_FILE = "solvers.txt";
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
     * String used to SPLIT list properties such as the delimiter list or the handler list.
     */
    private static final String SPLIT = ",";

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
    private static final String DEFAULT_MESSAGE_HANDLER =
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
     * If a props file does not contain a solver NAME or two files have the same NAME, unique names
     * have to be created because interacting with the solvers later requires uniqueness. The
     * counters are used for uniqueness.
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
        StringBuilder nameBuilder = new StringBuilder();
        nameBuilder.append(name);
        nameBuilder.append("_");
        nameBuilder.append(counter);
        counter++;
        NAME_COUNTERS.put(name, counter);
        // <NAME>_<counter> is now also a NAME that has been used and must be unique
        return uniqueName(nameBuilder.toString());
    }

    /**
     * Initializes {@link #SOLVERS} using the given hardcoded properties if that list is empty,
     * otherwise just returns the existing list.
     *
     * @return true iff SOLVERS was freshly initialized using the given solverProperties
     */
    public Collection<SolverType> getSolvers() {
        if (SOLVERS.isEmpty()) {
            for (Properties solverProp : loadSolvers()) {
                SolverType createdType = makeSolver(solverProp);
                SOLVERS.add(createdType);
                // If the solver is a LEGACY solver (only available in experimental mode),
                // add it to the separate list:
                if (SettingsConverter.read(solverProp, LEGACY, false)) {
                    LEGACY_SOLVERS.add(createdType);
                }
            }
        }
        return new ArrayList<>(SOLVERS);
    }

    /**
     * @return a copy of LEGACY_SOLVERS
     */
    public Collection<SolverType> getLegacySolvers() {
        getSolvers();
        return new ArrayList<>(LEGACY_SOLVERS);
    }

    /**
     * Create a {@link SolverTypeImplementation} from a Properties object.
     */
    private static SolverType makeSolver(Properties props) {
        String name;
        String command;
        String params;
        String version;
        String info;
        String preamble;
        String minVersion;
        long timeout;
        Class<?> solverSocketClass;
        Class<?> translatorClass;
        String[] handlerNames;
        String[] handlerOptions;
        String[] delimiters;

        // Read props file to create a SolverTypeImplementation object:

        // the solver's NAME has to be unique
        name = uniqueName(
            SettingsConverter.readRawString(props, SolverPropertiesLoader.NAME, DEFAULT_NAME));

        // default solver COMMAND, TIMEOUT, parameters, VERSION parameter, solver INFO (some string)
        command =
            SettingsConverter.readRawString(props, SolverPropertiesLoader.COMMAND, DEFAULT_COMMAND);
        timeout = SettingsConverter.read(props, SolverPropertiesLoader.TIMEOUT, DEFAULT_TIMEOUT);
        if (timeout < -1) {
            timeout = -1;
        }
        params =
            SettingsConverter.readRawString(props, SolverPropertiesLoader.PARAMS, DEFAULT_PARAMS);
        version =
            SettingsConverter.readRawString(props, SolverPropertiesLoader.VERSION, DEFAULT_VERSION);
        minVersion = SettingsConverter.readRawString(props, SolverPropertiesLoader.MIN_VERSION,
            DEFAULT_MINIMUM_VERSION);
        info = SettingsConverter.readRawString(props, SolverPropertiesLoader.INFO, DEFAULT_INFO);

        // the solver socket used for communication with the created solver
        try {
            String socketClassName = SettingsConverter.readRawString(props, SOLVER_SOCKET_CLASS,
                DEFAULT_MESSAGE_HANDLER);
            solverSocketClass = ClassLoaderUtil.getClassforName(socketClassName);
        } catch (ClassNotFoundException e) {
            solverSocketClass = Z3Socket.class;
        }


        // the message DELIMITERS used by the created solver in its stdout
        delimiters = SettingsConverter.readRawStringList(props, SolverPropertiesLoader.DELIMITERS,
            SPLIT, DEFAULT_DELIMITERS);

        // the smt translator (class SMTTranslator) used by the created solver
        try {
            String translatorClassName =
                SettingsConverter.readRawString(props, TRANSLATOR_CLASS, DEFAULT_TRANSLATOR);
            translatorClass = ClassLoaderUtil.getClassforName(translatorClassName);
        } catch (ClassNotFoundException e) {
            translatorClass = ModularSMTLib2Translator.class;
        }

        // the SMTHandlers used by the created solver
        // note that this will only take effect when using ModularSMTLib2Translator ...
        handlerNames = SettingsConverter.readRawStringList(props,
            SolverPropertiesLoader.HANDLER_NAMES, SPLIT, new String[0]);
        handlerOptions = SettingsConverter.readRawStringList(props,
            SolverPropertiesLoader.HANDLER_OPTIONS, SPLIT, new String[0]);

        // the solver specific preamble, may be null
        preamble = SettingsConverter.readFile(props, PREAMBLE_FILE, null);

        // create the solver type
        return new SolverTypeImplementation(name, info, params, command, version, minVersion,
            timeout, delimiters, translatorClass, handlerNames, handlerOptions, solverSocketClass,
            preamble);
    }

    /**
     * Loads the solvers that are specified in .props files in resource packages named
     * "de/uka/ilkd/key/smt/solvertypes".
     */
    private static Collection<Properties> loadSolvers() {
        Collection<Properties> completePropsList = new ArrayList<>();
        try {
            // load single solvers.txt files from the same location everywhere in the classpath
            for (Iterator<URL> it = SolverPropertiesLoader.class.getClassLoader()
                    .getResources(PACKAGE_PATH + SOLVER_LIST_FILE).asIterator(); it.hasNext();) {
                URL res = it.next();
                try (InputStream stream = res.openStream()) {
                    if (stream == null) {
                        continue;
                    }
                    // load solvers from this single solvers.txt
                    Collection<Properties> props = new ArrayList<>();
                    BufferedReader reader = new BufferedReader(new InputStreamReader(stream));
                    List<String> propsNames = reader.lines().collect(Collectors.toList());
                    for (String fileName : propsNames.stream().filter(n -> n.endsWith(".props"))
                            .collect(Collectors.toList())) {
                        Properties solverProp = new Properties();
                        InputStream propsFile =
                            SolverPropertiesLoader.class.getResourceAsStream(fileName);
                        try {
                            solverProp.load(propsFile);
                            props.add(solverProp);
                        } catch (Exception e) {
                            // every possible exception should be caught as loading the files
                            // should not break key
                            // if loading the props file does not work for any reason,
                            // create a warning and continue
                            LOGGER.warn(
                                String.format("Solver file %s could not be loaded.", fileName));
                        }
                    }
                    completePropsList.addAll(props);
                }
            }
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
        return completePropsList;
    }

}
