package de.uka.ilkd.key.smt.st;

import de.uka.ilkd.key.settings.PathConfig;
import de.uka.ilkd.key.smt.communication.SolverCommunicationSocket;
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
	private static String NAME = "name";
	private static String COMMAND = "command";
	private static String PARAMS = "params";
	private static String VERSION = "version";
	private static String DELIMITERS = "delimiters";
	private static String INFO = "info";
	private static String TIMEOUT = "timeout";
	private static String ITE = "ite";
	private static String LEGACY = "legacy";
	private static String SOCKET_MESSAGEHANDLER = "messageHandler";
	private static String SMTLIB_TRANSLATOR= "translatorClass";
	private static String DEFAULT_TRANSLATOR = "ModularSMTLib2Translator";
	private static String DEFAULT = "DEFAULT";
	private static String HANDLER_NAMES = "handlers";
	private static String[] DEFAULT_DELIMITERS = new String[] {"\r", "\n"};
	private static long DEFAULT_TIMEOUT = -1;
	private static boolean DEFAULT_ITE = false;

	/**
	 * Counter for default names.
	 * If a props file does not contain a solver name, it needs to get a default, unique
	 * one as the name is what makes SolverTypeImplementation objects distinguishable later on.
	 * The counter is used for uniqueness.
	 */
	private static int defaultNameCounter = 0;


	/**
	 * Methods to read from properties files.
	 * {@link de.uka.ilkd.key.settings.SettingsConverter} is not used as it expects
	 * delimiters that are not fit for humans to write or read.
	 */

	private static String readString(Properties props, String key, String defaultValue) {
		String value = props.getProperty(key);
		if (value == null) {
			value = defaultValue;
		}
		return value;
	}

	private static String[] readStringList(Properties props, String key, String[] defaultValue) {
		String value = props.getProperty(key);
		if (value == null) {
			return defaultValue;
		}
		return value.split(SPLIT);
	}

	private static boolean readBoolean(Properties props, String key, Boolean defaultValue) {
		return Boolean.parseBoolean(readString(props, key, defaultValue.toString()));
	}

	private static long readLong(Properties props, String key, Long defaultValue) {
		return Long.parseLong(readString(props, key, defaultValue.toString()));
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
				if (readBoolean(solverProp, LEGACY, false)) {
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
		String name, command, params, version, info, messageHandler;
		boolean supportsIfThenElse;
		long timeout;
		Class<?> translatorClass;
		String[] handlerNames;
		SolverCommunicationSocket.MessageHandler handler;
		String[] delimiters;

		// Read props file to create a SolverTypeImplementation object:

		name = readString(props, NAME, DEFAULT_NAME);
		// the solver's name has to be unique
		if (name.equals(DEFAULT_NAME)) {
			name = DEFAULT_NAME + defaultNameCounter;
			defaultNameCounter++;
		}

		// default solver command, timeout, parameters, version parameter, solver info (some string)
		command = readString(props, COMMAND, DEFAULT_COMMAND);
		timeout = readLong(props, TIMEOUT, DEFAULT_TIMEOUT);
		params = readString(props, PARAMS, DEFAULT_PARAMS);
		version = readString(props, VERSION, DEFAULT_VERSION);
		info = readString(props, INFO, DEFAULT_INFO);

		// does the solver support if-then-else?
		supportsIfThenElse = readBoolean(props, ITE, DEFAULT_ITE);

		// the communication socket used for communication with the created solver
		// (class SolverCommunicationSocket)
		messageHandler = readString(props, SOCKET_MESSAGEHANDLER, DEFAULT);
		handler = SolverCommunicationSocket.MessageHandler.valueOf(messageHandler);

		// the message delimiters used by the created solver in its stdout
		delimiters = readStringList(props, DELIMITERS, DEFAULT_DELIMITERS);

		// the smt translator (class SMTTranslator) used by the created solver
		try {
			String className = readString(props, SMTLIB_TRANSLATOR, DEFAULT_TRANSLATOR);
			translatorClass = ClassLoaderUtil.getClassforName(className);
		} catch (ClassNotFoundException e) {
			translatorClass = ModularSMTLib2Translator.class;
		}

		// the SMTHandlers used by the created solver
		// note that this will only take effect when using ModularSMTLib2Translator ...
		handlerNames = readStringList(props, HANDLER_NAMES, new String[0]);

		// create the solver object with the properties that have just been read
		return new SolverTypeImplementation(name, info, params, command, version, timeout, delimiters,
			supportsIfThenElse, translatorClass, handlerNames, handler);
	}

	/**
	 * Loads the solvers that are specified in .props files in the directory
	 * {@link PathConfig#getSmtSolverPropertiesDirectory()} into Properties objects and returns them.
	 */
	// TODO How to load multiple files from the resources folder at once WITHOUT knowing their name?
	private static Collection<Properties> loadSolvers() {
		InputStream stream = SolverPropertiesLoader.class.getResourceAsStream("defaultSolvers.txt");
		Collection<Properties> props = new ArrayList<>();
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
