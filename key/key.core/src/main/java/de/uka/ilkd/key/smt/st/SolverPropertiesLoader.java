package de.uka.ilkd.key.smt.st;

import de.uka.ilkd.key.settings.PathConfig;
import de.uka.ilkd.key.settings.SettingsConverter;
import de.uka.ilkd.key.smt.communication.SolverCommunicationSocket;

import java.io.*;
import java.util.*;

/**
 * Provides static SolverType objects to be reused and saves the properties to .props files.
 * Used to create {@link SolverType} (in the form of {@link ModifiableSolverType}) objects from .props files.
 */
public class SolverPropertiesLoader implements SolverTypes.SolverLoader {

	private static final Collection<SolverType> SOLVERS = new ArrayList<>(5);
	private static final Collection<SolverType> LEGACY_SOLVERS = new ArrayList<>(2);

	private static String DEFAULT_NAME = "SMT Solver";
	private static String DEFAULT_COMMAND = "";
	private static String DEFAULT_PARAMS = "";
	private static String DEFAULT_INFO = "An SMT solver.";
	private static String DEFAULT_VERSION = "";
	private static String[] DEFAULT_DELIMITERS = {};
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
	private static String METHOD_BUILDINGBLOCK = "[SolverTypeDefault]messageHandler";
	private static String DEFAULT = "DEFAULT";
	private static String LEGACY_TRANSLATION = "LEGACY_TRANSLATION";
	private static int defaultNameCounter = 0;

	/**
	 * Initializes {@link #SOLVERS} using the given hardcoded properties if that list is empty,
	 * otherwise just returns the existing list.
	 *
	 * @return true iff SOLVERS was freshly initialized using the given solverProperties
	 */
	@Override
	public Collection<SolverType> getSolvers() {
		if (SOLVERS.isEmpty()) {
			createHardcodedSolversProperties();
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
	 * Create a {@link ModifiableSolverType} from a Properties object.
	 */
	private static SolverType makeSolver(Properties props) {
		String name, command, params, version, info, buildingBlock, messageHandler;
		boolean supportsIfThenElse;
		long timeout;
		ModifiableSolverType.MethodBuildingBlocks buildingBlocks;
		SolverCommunicationSocket.MessageHandler handler;
		String[] delimiters;
		name = SettingsConverter.read(props, NAME, DEFAULT_NAME);
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
		boolean legacy = Boolean.valueOf(SettingsConverter.read(props, LEGACY, "false"));
		buildingBlock = SettingsConverter.read(props, METHOD_BUILDINGBLOCK, (legacy ? LEGACY_TRANSLATION : DEFAULT));
		handler = SolverCommunicationSocket.MessageHandler.valueOf(messageHandler);
		delimiters = new String[]{"\n", "\r"}; //TODO
		buildingBlocks = ModifiableSolverType.MethodBuildingBlocks.valueOf(buildingBlock);
		return new ModifiableSolverType(name, info, params, command, version, timeout,
				delimiters, supportsIfThenElse, buildingBlocks, handler);
	}

	/**
	 * Create the hardcoded solvers in {@link HardcodedSolver}.
	 * @return a map of unique solver names and the corresponding Properties objects describing the SolverTypes.
	 */
	private static Collection<Properties> createHardcodedSolversProperties() {
		Collection<Properties> propsList = new ArrayList<>(HardcodedSolver.values().length);
		for (HardcodedSolver hardcodedSolver : HardcodedSolver.values()) {
			Properties props = new Properties();
			SettingsConverter.store(props, NAME, hardcodedSolver.name);
			SettingsConverter.store(props, COMMAND, hardcodedSolver.command);
			SettingsConverter.store(props, PARAMS, hardcodedSolver.params);
			SettingsConverter.store(props, VERSION, hardcodedSolver.version);
			SettingsConverter.store(props, INFO, hardcodedSolver.info);
			SettingsConverter.store(props, TIMEOUT, hardcodedSolver.timeout);
			SettingsConverter.store(props, ITE, hardcodedSolver.supportsIfThenElse);
			if (hardcodedSolver.isLegacy()) {
				SettingsConverter.store(props, LEGACY, "true");
			}
			// TODO delimiters
			propsList.add(props);
			saveSolverProps(hardcodedSolver.name, props);
		}
		return propsList;
	}

	/**
	 * This may be used to automatically create some properties files for important solvers.
	 */
	public enum HardcodedSolver {

		Z3("Z3 (Legacy Translation)", "z3", "-in -smt2", new String[]{"\n", "\r", System.lineSeparator()},
				"--version", "Z3 solver by Microsoft", true, -1, true),

		Z3_NEW_TL("Z3", "z3", "-in -smt2", new String[]{"\n", "\r", System.lineSeparator()},
				"--version", "Z3 solver by Microsoft", true, -1, false),

		Z3_CE("Z3_CE", "z3", "-in -smt2", new String[]{"\n", "\r", System.lineSeparator()},
				"--version", "Z3 solver by Microsoft", true, -1, false),

		CVC4("CVC4 (Legacy Translation)", "cvc4",
				"--no-print-success -m --interactive --lang smt2",
				new String[]{"CVC4>"}, "--version", "CVC4 solver", true, -1, true),

		CVC4_NEW_TL("CVC4", "cvc4",
				"--no-print-success -m --interactive --lang smt2",
				new String[]{"CVC4>"}, "--version", "CVC4 solver", true, -1, false),

		CVC5("CVC5", "cvc5", "--interactive -m --lang smt2",
				new String[]{"cvc5>", "cvc5> "}, "--version", "CVC5 solver", true, -1, false);

		/*INVISMT("InViSMT", "invismt", "-in -smt2", new String[]{"\n", "\r", System.lineSeparator()},
				"--version", "Interactive SMT Solver wraps various SMT-Solvers", true,
				60, false);*/

		private String name, command, params, version, info;
		private String[] delimiters;
		private boolean supportsIfThenElse, isLegacy;
		private long timeout;

		HardcodedSolver(String name, String command, String params, String[] delimiters,
						String version, String info, boolean supportsIfThenElse, long timeout, boolean isLegacy) {
			this.name = name;
			this.command = command;
			this.params = params;
			this.version = version;
			this.timeout = timeout;
			this.delimiters = delimiters;
			this.supportsIfThenElse = supportsIfThenElse;
			this.info = info;
			this.isLegacy = isLegacy;
		}

		public boolean isLegacy() {
			return isLegacy;
		}

		public String getName() {
			return name;
		}

	}

	/**
	 * Loads the solvers that are specified in .props files in the directory
	 * {@link PathConfig#getSmtSolverPropertiesDirectory()} into Properties objects and returns them.
	 */
	private static Collection<Properties> loadSolvers() {
		File solverDir = new File(PathConfig.getSmtSolverPropertiesDirectory());
		Collection<Properties> props = new ArrayList<>();
		if (!solverDir.isDirectory()) {
			return new ArrayList<>(0);
		}
		for (File child : solverDir.listFiles(new FilenameFilter() {
			@Override
			public boolean accept(File dir, String name) {
				return name.endsWith(".props") && dir == solverDir;
			}
		})) {
			Properties solverProp = new Properties();
			try {
				solverProp.load(new FileInputStream(child));
				props.add(solverProp);
			} catch (IOException e) {
				continue;
			}
		}
		return props;
	}

	/**
	 * Saves a Properties object for a solver name to a .props file in the
	 * {@link PathConfig#getSmtSolverPropertiesDirectory()} directory.
	 */
	private static void saveSolverProps(String solverName, Properties solverProps) {
		File solverDir = new File(PathConfig.getSmtSolverPropertiesDirectory());
		if (!solverDir.mkdir() && !solverDir.isDirectory()) {
			return;
		}
		File solverProp = new File(solverDir, solverName + ".props");
		try (FileOutputStream out = new FileOutputStream(solverProp)) {
			solverProps.store(out, "Saved SMT solver info for: " + solverName);
		} catch (IOException e) {
			throw new RuntimeException(e);
		}
	}


}
