package de.uka.ilkd.key.smt.st;

import de.uka.ilkd.key.settings.PathConfig;
import de.uka.ilkd.key.settings.SettingsConverter;
import de.uka.ilkd.key.smt.AbstractSMTTranslator;
import de.uka.ilkd.key.smt.communication.SolverSocket;
import de.uka.ilkd.key.smt.newsmt2.ModularSMTLib2Translator;
import org.key_project.util.reflection.ClassLoaderUtil;

import java.io.*;
import java.util.*;
import java.util.stream.Collectors;

/**
 * Provides static SolverType objects to be reused and saves the properties to .props files.
 * Used to create {@link SolverType} (in the form of {@link SolverTypeImplementation}) objects from .props files.
 */
public class SolverPropertiesLoader implements SolverTypes.SolverLoader {

    private static final Collection<SolverType> SOLVERS = new ArrayList<>(5);
    private static final Collection<SolverType> LEGACY_SOLVERS = new ArrayList<>(2);


    /**
     * String used to split list properties such as the delimiter list or the handler list.
     */
    private static String SPLIT = ",";

    private static String DEFAULT_NAME = "SMT Solver";
    private static String DEFAULT_COMMAND = "";
    private static String DEFAULT_PARAMS = "";
    private static String DEFAULT_INFO = "An SMT solver.";
    private static String DEFAULT_VERSION = "";
    private static String DEFAULT_MINIMUM_VERSION = "";
    private static String NAME = "name";
    private static String COMMAND = "command";
    private static String PARAMS = "params";
    private static String VERSION = "version";
    private static String DELIMITERS = "delimiters";
    private static String INFO = "info";
    private static String TIMEOUT = "timeout";
    private static String ITE = "ite";
    private static String MINIMUM_VERSION = "minVersion";
    private static String LEGACY = "legacy";
    private static String SOCKET_MESSAGEHANDLER = "messageHandler";
    private static String SMTLIB_TRANSLATOR= "translatorClass";
    private static String DEFAULT_TRANSLATOR = "ModularSMTLib2Translator";
    private static String DEFAULT = "DEFAULT";
    private static String HANDLER_NAMES = "handlers";
    private static String PREAMBLE_FILE = "preamble";
    private static String[] DEFAULT_DELIMITERS = new String[] {"\n", "\r"};
    private static long DEFAULT_TIMEOUT = -1;
    private static boolean DEFAULT_ITE = false;

    /**
     * If a props file does not contain a solver name or two files have the same name,
     * unique names have to be created because interacting with the solvers later requires uniqueness.
     * The counters are used for uniqueness.
     */
    private static Map<String, Integer> nameCounters = new HashMap<>();

    private static String uniqueName(String name) {
        Integer counter = nameCounters.get(name);
        // if name has not been used yet, use it and set counter to 0
        if (counter == null) {
            nameCounters.put(name, 0);
            return name;
        }
        // if name was already used, use <name>_<counter> as name and increase counter afterwards
        StringBuilder nameBuilder = new StringBuilder();
        nameBuilder.append(name);
        nameBuilder.append("_");
        nameBuilder.append(counter);
        counter++;
        nameCounters.put(name, counter);
        // <name>_<counter> is now also a name that has been used and must be unique
        return uniqueName(nameBuilder.toString());
    }

    /**
     * Initializes {@link #SOLVERS} using the given hardcoded properties if that list is empty,
     * otherwise just returns the existing list.
     *
     * @return true iff SOLVERS was freshly initialized using the given solverProperties
     */
    @Override
    public Collection<SolverType> getSolvers() {
        if (SOLVERS.isEmpty()) {
            for (Properties solverProp : loadSolvers()) {
                SolverType createdType = makeSolver(solverProp);
                SOLVERS.add(createdType);
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
    @Override
    public Collection<SolverType> getLegacySolvers() {
        getSolvers();
        return new ArrayList<>(LEGACY_SOLVERS);
    }

    /**
     * Create a {@link SolverTypeImplementation} from a Properties object.
     */
    private static SolverType makeSolver(Properties props) {
        String name, command, params, version, info, messageHandler, preamble, minVersion;
        boolean supportsIfThenElse;
        long timeout;
        SolverSocket.MessageHandler handler;
        Class<?> translatorClass;
        String[] handlerNames;
        String[] delimiters;

        // Read props file to create a SolverTypeImplementation object:

        // the solver's name has to be unique
        name = uniqueName(SettingsConverter.readRawString(props, NAME, DEFAULT_NAME));

        // default solver command, timeout, parameters, version parameter, solver info (some string)
        command = SettingsConverter.readRawString(props, COMMAND, DEFAULT_COMMAND);
        timeout = SettingsConverter.read(props, TIMEOUT, DEFAULT_TIMEOUT);
        params = SettingsConverter.readRawString(props, PARAMS, DEFAULT_PARAMS);
        version = SettingsConverter.readRawString(props, VERSION, DEFAULT_VERSION);
        minVersion = SettingsConverter.readRawString(props, MINIMUM_VERSION, DEFAULT_MINIMUM_VERSION);
        info = SettingsConverter.readRawString(props, INFO, DEFAULT_INFO);

        // does the solver support if-then-else?
        supportsIfThenElse = SettingsConverter.read(props, ITE, DEFAULT_ITE);

        // the communication socket used for communication with the created solver
        // (class SolverCommunicationSocket)
        messageHandler = SettingsConverter.readRawString(props, SOCKET_MESSAGEHANDLER, DEFAULT);
        handler = SolverSocket.MessageHandler.valueOf(messageHandler);

        // the message delimiters used by the created solver in its stdout
        delimiters = SettingsConverter.readRawStringList(props, DELIMITERS, SPLIT, DEFAULT_DELIMITERS);

        // the smt translator (class SMTTranslator) used by the created solver
        try {
            String className = SettingsConverter.readRawString(props, SMTLIB_TRANSLATOR, DEFAULT_TRANSLATOR);
            translatorClass = ClassLoaderUtil.getClassforName(className);
        } catch (ClassNotFoundException e) {
            translatorClass = ModularSMTLib2Translator.class;
        }

        // the SMTHandlers used by the created solver
        // note that this will only take effect when using ModularSMTLib2Translator ...
        handlerNames = SettingsConverter.readRawStringList(props, HANDLER_NAMES, SPLIT, new String[0]);

        // the solver specific preamble, may be null
        preamble = SettingsConverter.readFile(props, PREAMBLE_FILE, null);
        return new SolverTypeImplementation(name, info, params, command, version,
                minVersion, timeout, delimiters, supportsIfThenElse, translatorClass, handlerNames, handler, preamble);
    }

    /**
     * Loads the solvers that are specified in .props files in the directory
     * {@link PathConfig#getSmtSolverPropertiesDirectory()} into Properties objects and returns them.
     */
    // TODO How to load multiple files from the resources folder at once WITHOUT knowing their name?
    private static Collection<Properties> loadSolvers() {
        InputStream stream = SolverPropertiesLoader.class.getResourceAsStream("defaultSolvers.txt");
        Collection<Properties> props = new ArrayList<>();
        // return an empty list if no defaultSolvers file was read
        if (stream == null) {
            return props;
        }
        BufferedReader reader = new BufferedReader(new InputStreamReader(stream));
        List<String> propsNames = reader.lines().collect(Collectors.toList());
        for (String fileName : propsNames) {
            Properties solverProp = new Properties();
            InputStream propsFile = SolverPropertiesLoader.class.getResourceAsStream(fileName);
            try {
                solverProp.load(propsFile);
                props.add(solverProp);
            } catch (IOException e) {
                continue;
            }
        }
        return props;
    }

}
