package de.uka.ilkd.key.smt.st;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.smt.*;
import de.uka.ilkd.key.smt.communication.SolverCommunicationSocket;
import de.uka.ilkd.key.smt.communication.ExternalProcessLauncher;
import de.uka.ilkd.key.smt.communication.SMTProcessLauncher;
import de.uka.ilkd.key.smt.communication.SolverCommunication;
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
 * - TODO
 */
public final class SolverTypeImplementation implements SolverType {

	/**
	 * The default values of this solver type object, final and private as they should not be changed after creation.
	 */
	private final String NAME, INFO, DEFAULT_PARAMS, DEFAULT_COMMAND, VERSION, MINIMUM_SUPPORTED_VERSION;
	private final long DEFAULT_TIMEOUT;
	private final String[] DELIMITERS;
	private final boolean ITE;
	/**
	 * The current command line parameters, timeout and command to be used instead of the default values, changeable.
	 */
	private String params, command;
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
	 * The version of the solver type at hand, returned by the actual program using the {@link #VERSION} cmd parameter.
	 */
	private String version;
	/**
	 * The names of the {@link de.uka.ilkd.key.smt.newsmt2.SMTHandler}s to be used by the {@link SMTTranslator}
	 * that is created with {@link #createTranslator(Services)}.
	 */
	private final String[] handlerNames;
	/**
	 * The {@link de.uka.ilkd.key.smt.communication.SolverCommunicationSocket.MessageHandler} used by
	 * the {@link SolverCommunicationSocket} created with {@link #getSocket(ModelExtractor)}.
	 */
	private final SolverCommunicationSocket.MessageHandler MSG_HANDLER;
	/**
	 * The class of the {@link SMTTranslator} to be created with {@link #createTranslator(Services)}.
	 */
	private final Class<?> TRANSLATOR_CLASS;
	/**
	 * The preamble String for the created {@link SMTTranslator}, may be null.
	 */
	@Nullable
	private final String preamble;

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

	/**
	 * Instantiate the solver type object with all its default values.
	 * The changeable values such as {@link #command} and {@link #params}
	 * are initially the same as their default values.
	 * @param name the name, e.g. "Z3"
	 * @param info some information about the solver type
	 * @param defaultParams the default command line PARAMETERS used to start the actual solver program
	 * @param defaultCommand the default command line COMMAND used to start the actual solver program
	 * @param version the command line parameter used to get the version of the actual solver program
	 * @param minimumSupportedVersion the minimum supported version of the solver type at hand
	 * @param defaultTimeout the default solver timeout for SMT processes using this solver type
	 * @param delimiters the message delimiters used by the actual solver program
	 * @param supportsIfThenElse whether the solver type at hand supports "ite" ? (TODO correct?)
	 * @param translatorClass the {@link SMTTranslator} class used by this solver type
	 * @param handlerNames the names of the {@link de.uka.ilkd.key.smt.newsmt2.SMTHandler}s to be used
	 *                        by the {@link SMTTranslator} created by this solver type
	 * @param messageHandler the {@link de.uka.ilkd.key.smt.communication.SolverCommunicationSocket.MessageHandler}
	 *                         used by the solver type at hand
	 * @param preamble the preamble String for the created {@link SMTTranslator}, may be null.
	 */
	public SolverTypeImplementation(String name, String info, String defaultParams, String defaultCommand,
									String version, String minimumSupportedVersion,
									long defaultTimeout, String[] delimiters, boolean supportsIfThenElse,
									Class<?> translatorClass, String[] handlerNames,
									SolverCommunicationSocket.MessageHandler messageHandler, String preamble) {
		NAME = name;
		INFO = info;
		DEFAULT_PARAMS = defaultParams;
		params = defaultParams;
		DEFAULT_COMMAND = defaultCommand;
		command = defaultCommand;
		DEFAULT_TIMEOUT = defaultTimeout;
		MINIMUM_SUPPORTED_VERSION = minimumSupportedVersion;
		timeout = defaultTimeout;
		DELIMITERS = delimiters;
		ITE = supportsIfThenElse;
		VERSION = version;
		TRANSLATOR_CLASS = translatorClass;
		// copy the array so that it cannot accidentally be manipulated from the outside
		this.handlerNames = Arrays.copyOf(handlerNames, handlerNames.length);
		MSG_HANDLER = messageHandler;
		this.preamble = preamble;
	}

	@Override
	public SMTSolver createSolver(SMTProblem problem, SolverListener listener, Services services) {
		// TODO Make this modifiable? (similar to SMTTranslator)
		return new SMTSolverImplementation(problem, listener, services, this);
	}

	@Override
	public String getName() {
		return NAME;
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
		return INFO;
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
		return DEFAULT_PARAMS;
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
		return DEFAULT_COMMAND;
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
		return DEFAULT_TIMEOUT;
	}

	// TODO services is never used
	@Override
	public SMTTranslator createTranslator(Services services) {
		Constructor<?>[] constructors = TRANSLATOR_CLASS.getConstructors();
		SMTTranslator smtTranslator = null;
		boolean instantiated = false;
		for (int i = 0; i < constructors.length; i++) {
			try {
				smtTranslator = (SMTTranslator) constructors[i].newInstance(handlerNames, preamble);
				/*translatorParams.stream().map(n -> {
					if (n.equals("<SERVICES>")) {
						return services;
					}
					return n;
				}).collect(Collectors.toList()));*/
				instantiated = true;
				break;
			} catch (IllegalArgumentException | ClassCastException | InstantiationException
					| IllegalAccessException | InvocationTargetException e) {
				instantiated = false;
				continue;
			}
		}
		// TODO different fallback option?
		if (!instantiated) {
			return new ModularSMTLib2Translator();
		}
		return smtTranslator;
	}

	@Override
	public String[] getDelimiters() {
		// Copy the delimiters array so that it cannot accidentally be manipulated from the outside.
		return Arrays.copyOf(DELIMITERS, DELIMITERS.length);
	}

	@Override
	public boolean supportsIfThenElse() {
		return ITE;
	}

	// TODO How to make this modifiable?
	@Override
	public String modifyProblem(String problem) {
		return problem;
	}

	@Override
	public String getVersionParameter() {
		return VERSION;
	}

	@Override
	public String getMinimumSupportedVersion() {
		return MINIMUM_SUPPORTED_VERSION;
	}

	@Override
	public String getVersion() {
		return version;
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

	@Override
	public boolean checkForSupport() {
		if (!isInstalled) {
			return false;
		}
		supportHasBeenChecked = true;
		version = getRawVersion();
		if (version == null) {
			version = "";
			isSupportedVersion = false;
			return false;
		}
		/*
		for (String supportedVersion : getSupportedVersions()) {
			if (version.indexOf(supportedVersion) > -1) {
				isSupportedVersion = true;
				return true;
			}
		} */
		// TODO is just comparing the actual version to the minimum version lexicographically enough?
		isSupportedVersion = version.compareTo(getMinimumSupportedVersion()) >= 0;
		return isSupportedVersion;
	}

	@Override
	public boolean supportHasBeenChecked() {
		return supportHasBeenChecked;
	}

	@Nonnull
	@Override
	public SolverCommunicationSocket getSocket(ModelExtractor query) {
		return new SolverCommunicationSocket(NAME, query, MSG_HANDLER);
	}

	@Nonnull
	@Override
	public SMTProcessLauncher getLauncher(SolverCommunication communication) {
		// TODO Make this modifiable? (similar to SMTTranslator)
		return new ExternalProcessLauncher(communication, getDelimiters());
	}

}
