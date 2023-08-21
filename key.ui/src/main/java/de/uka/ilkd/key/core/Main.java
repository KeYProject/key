/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.core;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.lang.reflect.InvocationTargetException;
import java.net.URL;
import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
import javax.xml.parsers.ParserConfigurationException;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.gui.ExampleChooser;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.WindowUserInterfaceControl;
import de.uka.ilkd.key.gui.lemmatagenerator.LemmataAutoModeOptions;
import de.uka.ilkd.key.gui.lemmatagenerator.LemmataHandler;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.SkipMacro;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.io.AutoSaver;
import de.uka.ilkd.key.proof.io.RuleSourceFactory;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.settings.PathConfig;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.ui.AbstractMediatorUserInterfaceControl;
import de.uka.ilkd.key.ui.ConsoleUserInterfaceControl;
import de.uka.ilkd.key.ui.Verbosity;
import de.uka.ilkd.key.util.CommandLine;
import de.uka.ilkd.key.util.CommandLineException;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.KeYConstants;
import de.uka.ilkd.key.util.rifl.RIFLTransformer;

import org.key_project.util.java.IOUtil;
import org.key_project.util.reflection.ClassLoaderUtil;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.xml.sax.SAXException;
import recoder.ParserException;

/**
 * The main entry point for KeY
 * <p>
 * This has been extracted from MainWindow to keep GUI and control further apart.
 */
public final class Main {
    /**
     * Command line options
     */
    private static final String HELP = "--help";
    private static final String SHOW_PROPERTIES = "--show-properties";
    private static final String AUTO = "--auto";
    private static final String LAST = "--last";
    private static final String AUTO_LOADONLY = "--auto-loadonly";
    private static final String AUTOSAVE = "--autosave";
    private static final String EXPERIMENTAL = "--experimental";
    /**
     * This parameter disables the possibility to prune in closed branches. It is meant as a
     * fallback solution if storing all closed goals needs too much memory.
     */
    private static final String NO_PRUNING_CLOSED = "--no-pruning-closed";
    /**
     * If this option is set, the (Disk)FileRepo does not delete its temporary directories (can be
     * used for debugging).
     */
    private static final String KEEP_FILEREPOS = "--keep-fileRepos";
    private static final String DEBUG = "--debug";
    private static final String MACRO = "--macro";
    private static final String NO_JMLSPECS = "--no-jmlspecs";
    private static final String TACLET_DIR = "--tacletDir";
    public static final String JUSTIFY_RULES = "--justify-rules";
    private static final String SAVE_ALL_CONTRACTS = "--save-all";
    private static final String TIMEOUT = "--timeout";
    private static final String EXAMPLES = "--examples";
    private static final String RIFL = "--rifl";
    public static final String JKEY_PREFIX = "--jr-";
    public static final String JMAX_RULES = JKEY_PREFIX + "maxRules";
    // deprecated
    // public static final String JPATH_OF_RULE_FILE = JKEY_PREFIX + "pathOfRuleFile";
    public static final String JPATH_OF_RESULT = JKEY_PREFIX + "pathOfResult";
    public static final String JTIMEOUT = JKEY_PREFIX + "timeout";
    public static final String JPRINT = JKEY_PREFIX + "print";
    public static final String JSAVE_RESULTS_TO_FILE = JKEY_PREFIX + "saveProofToFile";
    public static final String JFILE_FOR_AXIOMS = JKEY_PREFIX + "axioms";
    public static final String JFILE_FOR_DEFINITION = JKEY_PREFIX + "signature";
    private static final String VERBOSITY = "--verbose";

    /**
     * The user interface modes KeY can operate in.
     */
    private enum UiMode {
        /**
         * Interactive operation mode.
         */
        INTERACTIVE,

        /**
         * Auto operation mode.
         */
        AUTO
    }

    private static String examplesDir = null;

    /**
     * Determines which {@link UserInterfaceControl} is to be used.
     * <p>
     * By specifying <code>AUTO</code> as command line argument this will be set to
     * {@link UiMode#AUTO}, but {@link UiMode#INTERACTIVE} is the default.
     */
    private static UiMode uiMode = UiMode.INTERACTIVE;

    /**
     * Determines whether to actually prove or only load a problem when {@link Main#uiMode} is
     * {@link UiMode#AUTO}.
     * <p>
     * This can be controlled from the command line by specifying the argument
     * <code>AUTO_LOADONLY</code> instead of <code>AUTO</code>.
     */
    private static boolean loadOnly = false;

    /**
     * Object handling the parsing of commandline options
     */
    private static CommandLine cl;
    /**
     * flag whether recent loaded file should be loaded on startup
     */
    private static boolean loadRecentFile = false;

    /**
     * The file names provided on the command line
     */
    private static List<File> fileArguments;

    /**
     * Lists all features currently marked as experimental. Unless invoked with command line option
     * --experimental , those will be deactivated.
     */
    private static boolean experimentalMode;

    /**
     * Path to a RIFL specification file.
     */
    private static File riflFileName = null;

    /**
     * Save all contracts in selected location to automate the creation of multiple ".key"-files
     */
    private static boolean saveAllContracts = false;

    private static ProofMacro autoMacro = new SkipMacro();

    private static final Logger LOGGER = LoggerFactory.getLogger(Main.class);

    /**
     * <p>
     * This flag indicates if the example chooser should be shown if {@link #examplesDir} is defined
     * (not {@code null}). It is set in the Eclipse integration to {@code false}, because it is
     * required to define the path to a different one without showing the chooser.
     * </p>
     * <p>
     * Conclusion: It must be possible to use KeY with a custom examples directory without show in
     * the chooser on startup.
     * </p>
     */
    public static final boolean showExampleChooserIfExamplesDirIsDefined = true;

    private Main() {
    }

    public static void main(final String[] args) {
        Locale.setDefault(Locale.US);

        // does no harm on non macs
        System.setProperty("apple.laf.useScreenMenuBar", "true");

        Watchdog.start();

        try {
            cl = createCommandLine();
            cl.parse(args);
            evaluateOptions(cl);
            fileArguments = cl.getFileArguments();
            fileArguments = preProcessInput(fileArguments);
            AbstractMediatorUserInterfaceControl userInterface = createUserInterface(fileArguments);
            loadCommandLineFiles(userInterface, fileArguments);
        } catch (ExceptionInInitializerError e) {
            LOGGER.error("D'oh! It seems that KeY was not built properly!", e);
            System.exit(777);
        } catch (CommandLineException e) {
            printHeader(); // exception before verbosity option could be read
            LOGGER.error("Error in parsing the command: {}", e.getMessage());
            printUsageAndExit(true, e.getMessage(), -1);
        }

    }

    private static void logInformation() {
        LOGGER.debug("Java Version: {}", System.getProperty("java.version"));
        LOGGER.debug("Java Runtime: {}", System.getProperty("java.specification.version"));
        LOGGER.debug("Java VM: {}", System.getProperty("java.vm"));
        LOGGER.debug("OS: {}", System.getProperty("java.os"));
        LOGGER.debug("Hardware: {}", System.getProperty("java.hw"));
        Runtime rt = Runtime.getRuntime();
        LOGGER.debug("Total memory: {} MB", (rt.totalMemory() / 1048576.0));
        LOGGER.debug("Maximum memory:  {} MB", (rt.maxMemory() / 1048576.0));
        LOGGER.debug("Free memory: {} MB", (rt.freeMemory() / 1048576.0));
        LOGGER.debug("Available processors: {}", rt.availableProcessors());
    }

    public static void loadCommandLineFiles(AbstractMediatorUserInterfaceControl ui,
            List<File> fileArguments) {
        if (!fileArguments.isEmpty()) {
            ui.setMacro(autoMacro);
            ui.setSaveOnly(saveAllContracts);
            for (File f : fileArguments) {
                ui.loadProblem(f);
            }
            if (ui instanceof ConsoleUserInterfaceControl) {
                System.exit(((ConsoleUserInterfaceControl) ui).allProofsSuccessful ? 0 : 1);
            }
        } else if (Main.getExamplesDir() != null && Main.showExampleChooserIfExamplesDirIsDefined
                && ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                        .getShowLoadExamplesDialog()) {
            ui.openExamples();
        }
    }


    /**
     * Register commandline options with command line object
     *
     * @return commandline object
     */
    private static CommandLine createCommandLine() {
        CommandLine cl = new CommandLine();
        cl.setIndentation(3);
        cl.addSection("Using KeY");
        cl.addText("Usage: ./key [options] [filename]\n\n", false);
        cl.addSection("Options for the KeY-Prover");
        cl.addOption(HELP, null, "display this text");
        cl.addTextPart("--K-help", "display help for technical/debug parameters\n", true);
        cl.addOption(SHOW_PROPERTIES, null, "list all Java properties and exit");
        cl.addOption(LAST, null, "start prover with last loaded problem (only possible with GUI)");
        cl.addOption(AUTOSAVE, "<number>",
            "save intermediate proof states each n proof steps to a temporary location (default: 0 = off)");
        cl.addOption(EXPERIMENTAL, null, "switch experimental features on");
        cl.addOption(NO_PRUNING_CLOSED, null,
            "disables pruning and goal back in closed branches (saves memory)");
        cl.addOption(KEEP_FILEREPOS, null, "disables the automatic deletion of temporary"
            + "directories of file repos (for debugging)");
        cl.addSection("Batchmode options:");
        cl.addOption(TACLET_DIR, "<dir>",
            "load base taclets from a directory, not from internal structures");
        cl.addOption(DEBUG, null, "start KeY in debug mode");
        cl.addOption(AUTO, null,
            "start automatic prove procedure after initialisation without GUI");
        cl.addOption(AUTO_LOADONLY, null, "load files automatically without proving (for testing)");
        cl.addOption(VERBOSITY, "<number>", "verbosity");
        cl.addOption(NO_JMLSPECS, null, "disable parsing JML specifications");
        cl.addOption(EXAMPLES, "<directory>",
            "load the directory containing the example files on startup");
        cl.addOption(RIFL, "<filename>",
            "load RIFL specifications from file (requires GUI and startup file)");
        cl.addOption(MACRO, "<proofMacro>", "apply automatic proof macro");
        cl.addOption(SAVE_ALL_CONTRACTS, null,
            "save all selected contracts for automatic execution");
        cl.addOption(TIMEOUT, "<timeout>",
            "timeout for each automatic proof of a problem in ms (default: "
                + LemmataAutoModeOptions.DEFAULT_TIMEOUT + ", i.e., no timeout)");
        cl.addSection("Options for justify rules:");
        cl.addOption(JUSTIFY_RULES, "<filename>",
            "autoprove taclets (options always with prefix --jr) needs the path to the rule file as argument");
        cl.addText("\n", true);
        cl.addText(
            "The '" + JUSTIFY_RULES + "' option has a number of additional parameters you can set.",
            false);
        cl.addText("The following options only apply if '" + JUSTIFY_RULES + "' is used.", false);
        cl.addText("\n", true);
        cl.addOption(JMAX_RULES, "<number>",
            "maximum number of rule application to perform (default: "
                + LemmataAutoModeOptions.DEFAULT_MAXRULES + ")");
        cl.addOption(JPATH_OF_RESULT, "<path>", "store proofs to this folder");
        cl.addOption(JTIMEOUT, "<timeout>", "the timeout for proof of a taclet in ms (default: "
            + LemmataAutoModeOptions.DEFAULT_TIMEOUT + ")");
        cl.addOption(JPRINT, "<terminal/disable>", "send output to terminal or disable output");
        cl.addOption(JSAVE_RESULTS_TO_FILE, "<true/false>",
            "save or drop proofs (then stored to path given by " + JPATH_OF_RESULT + ")");
        cl.addOption(JFILE_FOR_AXIOMS, "<filename>", "read axioms from given file");
        cl.addOption(JFILE_FOR_DEFINITION, "<filename>", "read definitions from given file");
        return cl;
    }

    /**
     * Evaluate the commandline options
     *
     * @param cl parsed command lines, not null
     */
    public static void evaluateOptions(CommandLine cl) {
        Integer verbosity = null;
        // this property overrides the default
        if (Boolean.getBoolean("key.verbose-ui")) {
            verbosity = Verbosity.TRACE;
        }
        if (cl.isSet(VERBOSITY)) { // verbosity
            try {
                verbosity = cl.getInteger(VERBOSITY, Verbosity.DEBUG);
            } catch (CommandLineException e) {
                LOGGER.warn("Failed to read verbosity", e);
            }
        }

        Log.configureLogging(verbosity);
        logInformation();

        if (cl.isSet(EXPERIMENTAL)) {
            LOGGER.info("Running in experimental mode ...");
            setEnabledExperimentalFeatures(true);
        } else {
            setEnabledExperimentalFeatures(false);
        }

        printHeader();

        if (cl.isSet(SHOW_PROPERTIES)) {
            try {
                java.util.Properties props = System.getProperties();
                for (var e : props.entrySet()) {
                    LOGGER.info("Property: {} = {}", e.getKey(), e.getValue());
                }
            } finally {
                System.exit(0);
            }
        }

        if (cl.isSet(AUTO)) {
            uiMode = UiMode.AUTO;

        }
        if (cl.isSet(AUTO_LOADONLY)) {
            uiMode = UiMode.AUTO;
            loadOnly = true;
        }

        if (cl.isSet(AUTOSAVE)) {
            try {
                int eachSteps = cl.getInteger(AUTOSAVE, 0);
                if (eachSteps < 0) {
                    printUsageAndExit(false, "Illegal autosave period (must be a number >= 0)", -5);
                }
                AutoSaver.setDefaultValues(eachSteps, uiMode == UiMode.INTERACTIVE);
            } catch (CommandLineException e) {
                LOGGER.error("Failed to read integer", e);
            }
        }

        if (cl.isSet(HELP)) {
            // 0 as exit value means: no error
            printUsageAndExit(true, null, 0);
        }

        if (cl.isSet(NO_JMLSPECS)) {
            GeneralSettings.disableSpecs = true;
        }

        if (cl.isSet(TIMEOUT)) {
            LOGGER.info("Timeout is set");
            long timeout = -1;
            try {
                timeout = cl.getLong(TIMEOUT, -1);
                LOGGER.info("Timeout is: {} ms", timeout);
            } catch (CommandLineException e) {
                LOGGER.error("Failed to read long", e);
            }

            if (timeout < -1) {
                printUsageAndExit(false, "Illegal timeout (must be a number >= -1)", -5);
            }

            ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setTimeout(timeout);
        }

        if (cl.isSet(EXAMPLES)) {
            examplesDir = cl.getString(EXAMPLES, null);
        }

        if (Debug.ENABLE_DEBUG) {
            LOGGER.info("Running in debug mode");
        }

        if (Debug.ENABLE_ASSERTION) {
            LOGGER.info("Using assertions");
        } else {
            LOGGER.info("Not using assertions");
        }

        if (cl.isSet(EXPERIMENTAL)) {
            LOGGER.info("Running in experimental mode ...");
            setEnabledExperimentalFeatures(true);
        } else {
            setEnabledExperimentalFeatures(false);
        }

        if (cl.isSet(RIFL)) {
            riflFileName = new File(cl.getString(RIFL, null));
            LOGGER.info("Loading RIFL specification from {}", riflFileName);
        }

        if (cl.isSet(LAST)) {
            loadRecentFile = true;
        }

        if (cl.isSet(JUSTIFY_RULES)) {
            evaluateLemmataOptions(cl);
        }

        if (cl.isSet(DEBUG)) {
            Debug.ENABLE_DEBUG = true;
        }

        if (cl.isSet(MACRO)) {
            String macro = cl.getString(MACRO, "");
            for (ProofMacro m : ClassLoaderUtil.loadServices(ProofMacro.class)) {
                if (macro.equals(m.getClass().getSimpleName())) {
                    // memorize macro for later
                    try {
                        autoMacro = m.getClass().getDeclaredConstructor().newInstance();
                    } catch (InstantiationException e) {
                        LOGGER.warn("Automatic proof macro can not be instantiated!", e);
                    } catch (IllegalAccessException e) {
                        LOGGER.warn("Automatic proof macro can not be accessed!", e);
                    } catch (InvocationTargetException e) {
                        LOGGER.warn("Automatic proof macro can not be invoked!", e);
                    } catch (NoSuchMethodException e) {
                        LOGGER.warn("Automatic proof macro can not be called!", e);
                    }
                    break;
                }
            }
            if (macro.equals("") || autoMacro instanceof SkipMacro) {
                LOGGER.warn("No automatic proof macro specified.");
            }
        }

        if (cl.isSet(SAVE_ALL_CONTRACTS)) {
            saveAllContracts = true;
        }

        if (cl.isSet(TACLET_DIR)) {
            System.setProperty(RuleSourceFactory.STD_TACLET_DIR_PROP_KEY,
                cl.getString(TACLET_DIR, ""));
        }

        if (cl.isSet(NO_PRUNING_CLOSED)) {
            GeneralSettings.noPruningClosed = false;
        }

        if (cl.isSet(KEEP_FILEREPOS)) {
            GeneralSettings.keepFileRepos = true;
        }
    }

    /**
     * Deactivate experimental features.
     */
    public static void setEnabledExperimentalFeatures(boolean state) {
        experimentalMode = state;
        LOGGER.debug("Experimental Features: {}", state);
    }

    public static boolean isExperimentalMode() {
        return experimentalMode;
    }

    /**
     * Print a header text on to the console.
     */
    private static void printHeader() {
        LOGGER.info("KeY Version {}", KeYConstants.VERSION);
        LOGGER.info(KeYConstants.COPYRIGHT);
        LOGGER.info("KeY is protected by the GNU General Public License");
    }

    /**
     * Initializes the {@link UserInterfaceControl} to be used by KeY.
     * <p>
     * {@link ConsoleUserInterfaceControl} will be used if {@link Main#uiMode} is
     * {@link UiMode#AUTO} and {@link WindowUserInterfaceControl} otherwise.
     *
     * @return a <code>UserInterfaceControl</code> based on the value of <code>uiMode</code>
     */
    private static AbstractMediatorUserInterfaceControl createUserInterface(
            List<File> fileArguments) {

        if (uiMode == UiMode.AUTO) {
            // terminate immediately when an uncaught exception occurs (e.g., OutOfMemoryError), see
            // bug #1216
            Thread.setDefaultUncaughtExceptionHandler((t, e) -> {
                LOGGER.error("Auto mode was terminated by an exception:", e);
                final String msg = e.getMessage();
                if (msg != null) {
                    LOGGER.info(msg);
                }
                System.exit(-1);
            });
            if (fileArguments.isEmpty()) {
                printUsageAndExit(true, "Error: No file to load from.", -4);
            }

            return new ConsoleUserInterfaceControl(loadOnly);
        } else {
            /*
             * explicitly enable pruning in closed branches for interactive mode (if not manually
             * disabled)
             */
            GeneralSettings.noPruningClosed = cl.isSet(NO_PRUNING_CLOSED);

            MainWindow mainWindow = MainWindow.getInstance();

            if (loadRecentFile) {
                String mostRecent = mainWindow.getRecentFiles().getMostRecent();

                if (mostRecent != null) {
                    File mostRecentFile = new File(mostRecent);
                    if (mostRecentFile.exists()) {
                        fileArguments.add(mostRecentFile);
                    } else {
                        LOGGER.info("File does not exist anymore: {}", mostRecentFile);
                    }
                }
            }
            ensureExamplesAvailable();
            return mainWindow.getUserInterface();
        }

    }

    public static void ensureExamplesAvailable() {
        File examplesDir = getExamplesDir() == null ? ExampleChooser.lookForExamples()
                : new File(getExamplesDir());
        if (!examplesDir.exists()) {
            examplesDir = setupExamples();
        }
        setExamplesDir(examplesDir.getAbsolutePath());
    }

    private static File setupExamples() {
        try {
            URL examplesURL = Main.class.getResource("/examples.zip");
            if (examplesURL == null) {
                throw new IOException("Missing examples.zip in resources");
            }

            File tempDir = createTempDirectory();

            if (tempDir != null) {
                IOUtil.extractZip(examplesURL.openStream(), tempDir.toPath());
            }
            return tempDir;
        } catch (IOException e) {
            LOGGER.warn("Error setting up examples", e);
            return null;
        }
    }


    private static File createTempDirectory() throws IOException {
        final File tempDir = File.createTempFile("keyheap-examples-", null);
        tempDir.delete();
        if (!tempDir.mkdir()) {
            return null;
        }
        Runtime.getRuntime().addShutdownHook(new Thread(() -> IOUtil.delete(tempDir)));
        return tempDir;
    }

    private static void evaluateLemmataOptions(CommandLine options) {

        LemmataAutoModeOptions opt;
        try {

            opt = new LemmataAutoModeOptions(options, KeYConstants.INTERNAL_VERSION,
                PathConfig.getKeyConfigDir());
            LemmataHandler handler = new LemmataHandler(opt, AbstractProfile.getDefaultProfile());
            handler.start();

        } catch (Exception e) {
            if (Debug.ENABLE_DEBUG) {
                LOGGER.warn("Lemmata options failed", e);
            }
            printUsageAndExit(false, e.getMessage(), -2);
        }

    }

    public static void printUsageAndExit(boolean printUsage, String offending, int exitValue) {
        PrintStream ps = exitValue == 0 ? System.out : System.err;
        if (offending != null) {
            ps.println(offending);
        }
        if (printUsage) {
            cl.printUsage(ps);
        }
        System.exit(exitValue);
    }

    /**
     * Used by {@link de.uka.ilkd.key.gui.KeYFileChooser} (and potentially others) to determine
     * working directory. In case there is at least one location (i.e. a file or directory)
     * specified as command line argument, working directory is determined based on first location
     * that occurred in the list of arguments. Otherwise, value of System.getProperty("user.home")
     * is used to determine working directory.
     *
     * @return {@link File} object representing working directory.
     */
    public static File getWorkingDir() {
        if (fileArguments != null && !fileArguments.isEmpty()) {
            File f = fileArguments.get(0);
            if (f.isDirectory()) {
                return f;
            } else {
                return f.getParentFile();
            }
        } else {
            return IOUtil.getCurrentDirectory();
        }
    }

    /**
     * Perform necessary actions before loading any problem files. Currently only performs RIFL to
     * JML transformation.
     */
    private static List<File> preProcessInput(List<File> filesOnStartup) {
        List<File> result = new ArrayList<>();
        // RIFL to JML transformation
        if (riflFileName != null) {
            if (filesOnStartup.isEmpty()) {
                LOGGER.info("[RIFL] No Java file to load from.");
                System.exit(-130826);
            }
            // only use one input file
            File fileNameOnStartUp = filesOnStartup.get(0).getAbsoluteFile();
            // final KeYRecoderExceptionHandler kexh = ui.getMediator().getExceptionHandler();
            try {
                RIFLTransformer transformer = new RIFLTransformer();
                transformer.doTransform(riflFileName, fileNameOnStartUp,
                    RIFLTransformer.getDefaultSavePath(fileNameOnStartUp));

                LOGGER.info("[RIFL] Writing transformed Java files to {}  ...",
                    fileNameOnStartUp);
                return transformer.getProblemFiles();
            } catch (ParserConfigurationException | SAXException | ParserException
                    | IOException e) {
                LOGGER.warn("rifl transform failed", e);
            }

            return result;
        }
        // nothing to do, pass the original files
        return filesOnStartup;
    }

    public static String getExamplesDir() {
        return examplesDir;
    }

    /**
     * Defines the examples directory. This method is used by the Eclipse integration (KeY4Eclipse)
     * to use the examples extract from the plug-in into the workspace.
     *
     * @param newExamplesDir The new examples directory to use.
     */
    public static void setExamplesDir(String newExamplesDir) {
        examplesDir = newExamplesDir;
    }
}
