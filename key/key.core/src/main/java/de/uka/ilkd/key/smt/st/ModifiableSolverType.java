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
public final class ModifiableSolverType implements SolverType {

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
	private final MethodBuildingBlocks BUILDING_BLOCKS;
	private final SolverCommunicationSocket.MessageHandler MSG_HANDLER;

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

	public ModifiableSolverType(String name, String info, String defaultParams, String defaultCommand, String version,
								long defaultTimeout, String[] delimiters, boolean supportsIfThenElse,
								MethodBuildingBlocks buildingBlocks, SolverCommunicationSocket.MessageHandler handler) {
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
		BUILDING_BLOCKS = buildingBlocks;
		MSG_HANDLER = handler;
	}

	/**
	 * Create a new ModifiableSolverType with {@link MethodBuildingBlocks}.
	 */
	public ModifiableSolverType(String name, String info, String defaultParams, String defaultCommand, String version,
								long defaultTimeout, String[] delimiters, boolean supportsIfThenElse,
								SolverCommunicationSocket.MessageHandler handler) {
		this(name, info, defaultParams, defaultCommand, version, defaultTimeout, delimiters, supportsIfThenElse,
				MethodBuildingBlocks.DEFAULT, handler);
	}

	@Override
	public SMTSolver createSolver(SMTProblem problem, SolverListener listener, Services services) {
		return BUILDING_BLOCKS.createSolver(this, problem, listener, services);
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
		return BUILDING_BLOCKS.createTranslator(this, services);
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

	@Override
	public String modifyProblem(String problem) {
		return BUILDING_BLOCKS.modifyProblem(this, problem);
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

	@Override
	public String getRawVersion() {
		return BUILDING_BLOCKS.getRawVersion(this);
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
		return BUILDING_BLOCKS.getLauncher(communication, this);
	}


	public enum MethodBuildingBlocks {

		DEFAULT,

		LEGACY_TRANSLATION {
			@Override
			SMTTranslator createTranslator(SolverType type, Services services) {
				// TODO mentionLogic was false for Z3...
				return new SmtLib2Translator(services,
						new AbstractSMTTranslator.Configuration(false, true));
			}
		};

		SMTProcessLauncher getLauncher(SolverCommunication communication, SolverType type) {
			return new ExternalProcessLauncher(communication, type.getDelimiters());
		}

		String getRawVersion(SolverType type) {
			if (type.isInstalled(true)) {
				return VersionChecker.INSTANCE.getVersionFor(type.getSolverCommand(), type.getVersionParameter());
			} else {
				return null;
			}
		}

		SMTTranslator createTranslator(SolverType type, Services services) {
			return new ModularSMTLib2Translator();
		}

		SMTSolver createSolver(SolverType type, SMTProblem problem, SolverListener listener, Services services) {
			return new SMTSolverImplementation(problem, listener, services, type);
		}

		String modifyProblem(SolverType type, String problem) {
			return problem;
		}

	}
}
