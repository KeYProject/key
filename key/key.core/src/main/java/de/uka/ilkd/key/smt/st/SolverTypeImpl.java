package de.uka.ilkd.key.smt.st;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.smt.*;
import de.uka.ilkd.key.smt.communication.SolverCommunicationSocket;
import de.uka.ilkd.key.smt.communication.ExternalProcessLauncher;
import de.uka.ilkd.key.smt.communication.SMTProcessLauncher;
import de.uka.ilkd.key.smt.communication.SolverCommunication;
import de.uka.ilkd.key.smt.newsmt2.ModularSMTLib2Translator;

import javax.annotation.Nonnull;
import java.io.File;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * Final SolverType implementation that uses building blocks for the various methods.
 * This can be used to modify a ModifiableSolverType object using .props files only,
 * for example (see {@link SolverPropertiesLoader}).
 * <p>
 * The building blocks that can be modified on creation are:
 * - The various String parameters such as default command, params and the name
 * - TODO
 */
public final class SolverTypeImpl implements SolverType {

	private final String NAME, INFO, DEFAULT_PARAMS, DEFAULT_COMMAND, VERSION;
	private final long DEFAULT_TIMEOUT;
	private String params, command;
	private final String[] DELIMITERS;
	private final boolean ITE;
	private long timeout;
	private boolean supportHasBeenChecked = false;
	private String version;
	private boolean isSupportedVersion = false;
	private boolean installWasChecked = false;
	private boolean isInstalled = false;
	private final String[] handlerNames;
	private final SolverCommunicationSocket.MessageHandler MSG_HANDLER;
	private final Class<?> TRANSLATOR_CLASS;
	private final List<Object> translatorParams;

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

	public SolverTypeImpl(String name, String info, String defaultParams, String defaultCommand,
						  String version,
						  long defaultTimeout, String[] delimiters, boolean supportsIfThenElse,
						  Class<?> translatorClass, String[] handlerNames,
						  List<Object> translatorParams,
						  SolverCommunicationSocket.MessageHandler handler) {
		NAME = name;
		INFO = info;
		DEFAULT_PARAMS = defaultParams;
		params = defaultParams;
		DEFAULT_COMMAND = defaultCommand;
		command = defaultCommand;
		DEFAULT_TIMEOUT = defaultTimeout;
		timeout = defaultTimeout;
		DELIMITERS = delimiters;
		ITE = supportsIfThenElse;
		VERSION = version;
		TRANSLATOR_CLASS = translatorClass;
		this.handlerNames = handlerNames;
		MSG_HANDLER = handler;
		this.translatorParams = new ArrayList<>(translatorParams);
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

	@Override
	public SMTTranslator createTranslator(Services services) {
		Constructor<?>[] constructors = TRANSLATOR_CLASS.getConstructors();
		SMTTranslator smtTranslator = null;
		boolean instantiated = false;
		for (int i = 0; i < constructors.length; i++) {
			try {
				smtTranslator = (SMTTranslator) constructors[i].newInstance((Object) handlerNames);
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
	public String[] getSupportedVersions() {
		// TODO
		return new String[]{"none"};
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
		// TODO: contained in getSupportedVersions -> depends on whether that is kept...
		return false;
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
		for (String supportedVersion : getSupportedVersions()) {
			if (version.indexOf(supportedVersion) > -1) {
				isSupportedVersion = true;
				return true;
			}
		}
		isSupportedVersion = false;
		return false;
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
