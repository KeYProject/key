package de.uka.ilkd.key.smt.st;

import de.uka.ilkd.key.settings.PathConfig;
import de.uka.ilkd.key.settings.SettingsConverter;
import de.uka.ilkd.key.smt.communication.SolverCommunicationSocket;
import de.uka.ilkd.key.smt.newsmt2.ModularSMTLib2Translator;
import org.key_project.util.reflection.ClassLoaderUtil;

import java.io.*;
import java.util.*;
import java.util.stream.Collectors;

/**
 * Provides static SolverType objects to be reused and saves the properties to .props files.
 * Used to create {@link SolverType} (in the form of {@link SolverTypeImpl}) objects from .props files.
 */
public class SolverPropertiesLoader implements SolverTypes.SolverLoader {

	private static final Collection<SolverType> SOLVERS = new ArrayList<>(5);
	private static final Collection<SolverType> LEGACY_SOLVERS = new ArrayList<>(2);

	private static String DEFAULT_NAME = "SMT Solver";
	private static String DEFAULT_COMMAND = "";
	private static String DEFAULT_PARAMS = "";
	private static String DEFAULT_INFO = "An SMT solver.";
	private static String DEFAULT_VERSION = "";
	private static String DEFAULT_DELIMITERS = "\n <delim_split> \r";
	private static long DEFAULT_TIMEOUT = -1;
	private static boolean DEFAULT_ITE = false;
	private static String NAME = "[SolverTypeDefault]name";
	private static String COMMAND = "[SolverTypeDefault]command";
	private static String PARAMS = "[SolverTypeDefault]params";
	private static String VERSION = "[SolverTypeDefault]version";
	private static String DELIMITERS = "[SolverTypeDefault]delimiters";
	private static String INFO = "[SolverTypeDefault]info";
	private static String TIMEOUT = "[SolverTypeDefault]timeout";
	private static String ITE = "[SolverTypeDefault]ite";
	private static String LEGACY = "[SolverTypeDefault]legacy";
	private static String SOCKET_MESSAGEHANDLER = "[SolverTypeDefault]messageHandler";
	private static String SMTLIB_TRANSLATOR= "[SolverTypeDefault]translatorClass";
	private static String DEFAULT_TRANSLATOR = "ModularSMTLib2Translator";
	private static String DEFAULT = "DEFAULT";
	private static String TRANSLATOR_PARAMS = "[SolverTypeDefault]translatorParams";
	private static String DEFAULT_TRANSLATOR_PARAMS = "\\\\";
	private static int defaultNameCounter = 0;

	private static String DELIMITER_SPLIT = " <delim_split> ";

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
				if (Boolean.valueOf(SettingsConverter.read(solverProp, LEGACY, "false"))) {
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
	 * Create a {@link SolverTypeImpl} from a Properties object.
	 */
	private static SolverType makeSolver(Properties props) {
		String name, command, params, version, info, messageHandler;
		boolean supportsIfThenElse;
		long timeout;
		Class<?> translatorClass;
		List<Object> translatorParams = new ArrayList<>(0);
		SolverCommunicationSocket.MessageHandler handler;
		String[] delimiters;
		name = SettingsConverter.read(props, NAME, DEFAULT_NAME);
		// The solver's name has to be unique
		if (name.equals(DEFAULT_NAME)) {
			name = DEFAULT_NAME + defaultNameCounter;
			defaultNameCounter++;
		}
		command = SettingsConverter.read(props, COMMAND, DEFAULT_COMMAND);
		params = SettingsConverter.read(props, PARAMS, DEFAULT_PARAMS);
		version = SettingsConverter.read(props, VERSION, DEFAULT_VERSION);
		info = SettingsConverter.read(props, INFO, DEFAULT_INFO);
		supportsIfThenElse = Boolean.valueOf(SettingsConverter.read(props, ITE, DEFAULT_ITE));
		timeout = Long.valueOf(SettingsConverter.read(props, TIMEOUT, DEFAULT_TIMEOUT));
		messageHandler = SettingsConverter.read(props, SOCKET_MESSAGEHANDLER, DEFAULT);
		delimiters = SettingsConverter.read(props, DELIMITERS, DEFAULT_DELIMITERS).split(DELIMITER_SPLIT);
		try {
			translatorClass = ClassLoaderUtil.getClassforName(
					SettingsConverter.read(props, SMTLIB_TRANSLATOR, DEFAULT_TRANSLATOR));
		} catch (ClassNotFoundException e) {
			translatorClass = ModularSMTLib2Translator.class;
		}
		for (String str: SettingsConverter.read(props, TRANSLATOR_PARAMS, DEFAULT_TRANSLATOR_PARAMS)
				.split("\\\\")) {
			translatorParams.add(ParamConverter.convert(str));
		}
		handler = SolverCommunicationSocket.MessageHandler.valueOf(messageHandler);
		return new SolverTypeImpl(name, info, params, command, version, timeout,
				delimiters, supportsIfThenElse, translatorClass, translatorParams, handler);
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


	private static class ParamConverter {

		private static Object convert(String str) {
			// TODO: example str.equals "AbstractSMTTranslator.Configuration(false, true)" -> create the object
			return str;
		}
	}

}
