/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.core;

import java.io.File;
import java.io.IOException;
import java.lang.reflect.InvocationTargetException;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Locale;
import java.util.concurrent.Callable;
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
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.ui.AbstractMediatorUserInterfaceControl;
import de.uka.ilkd.key.ui.ConsoleUserInterfaceControl;
import de.uka.ilkd.key.ui.Verbosity;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.KeYConstants;
import de.uka.ilkd.key.util.rifl.RIFLTransformer;

import org.key_project.util.java.IOUtil;
import org.key_project.util.reflection.ClassLoaderUtil;

import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.xml.sax.SAXException;
import picocli.CommandLine;
import picocli.CommandLine.Option;
import picocli.CommandLine.Parameters;
import recoder.ParserException;

/**
 * The main entry point for KeY
 * <p>
 * This has been extracted from MainWindow to keep GUI and control further
 * apart.
 */
public final class Main implements Callable<Integer> {
    private static final Logger LOGGER = LoggerFactory.getLogger(Main.class);
    private static Path workingDir;


    // @Option(names = "--help", description = "display this text")
    // private boolean showHelp = false;

    @Option(names = "--K-help", description = "display help for technical/debug parameters")
    private boolean showKHelp = false;

    @Option(names = "--show-properties", description = "list all Java properties and exit")
    private boolean showProperties = false;

    @Option(names = "--auto",
        description = "start automatic prove procedure after initialisation without GUI")
    private boolean isAuto = false;

    /**
     * flag whether recent loaded file should be loaded on startup
     */
    @Option(names = "--last",
        description = "flag whether recent loaded file should be loaded on startup")
    private boolean loadRecentFile = false;

    @Option(names = "--auto-loadonly",
        description = "load files automatically without proving (for testing)")
    private boolean isAutoLoadOnly = false;

    @Option(names = "--autosave",
        paramLabel = "number",
        description = "save intermediate proof states each n proof steps to a temporary location (default: 0 = off)",
        defaultValue = "0")
    private int autoSaveSteps = 0;

    /**
     * Lists all features currently marked as experimental. Unless invoked with
     * command line option --experimental , those will be deactivated.
     */
    @Deprecated(since = "2.13.0")
    @Option(names = "--experimental", description = "switch experimental features on")
    private boolean isExperimental = false;

    /**
     * This parameter disables the possibility to prune in
     * closed branches. It is meant as a fallback solution
     * if storing all closed goals needs too much memory.
     */
    @Option(names = "--no-pruning-closed",
        description = "disables pruning and goal back in closed branches (saves memory)")

    private boolean isNoPruningClosed = false;
    /**
     * If this option is set, the (Disk)FileRepo does not delete its temporary
     * directories (can be
     * used for debugging).
     */
    @Option(names = "--keep-fileRepos", description = "disables the automatic deletion of temporary"
        + "directories of file repos (for debugging)")

    private boolean isKeepFileRepos = false;

    @Option(names = "--debug", description = "start KeY in debug mode")
    private boolean debug = false;

    @Option(names = "--macro", paramLabel = "STRING", description = "apply automatic proof macro")
    private @Nullable String macro = null;

    @Option(names = "--no-jmlspecs", description = "disable parsing JML specifications")
    private boolean noJmlSpecs = false;

    @Option(names = "--tacletDir",
        description = "load base taclets from a directory, not from internal structures",
        paramLabel = "FOLDER")
    private @Nullable Path tacletDir = null;

    @Option(names = "--examples", paramLabel = "FOLDER",
        description = "load the directory containing the example files on startup")
    private @Nullable String examplesFolder = null;

    /**
     * Path to a RIFL specification file.
     */
    @Option(names = "--rifl", paramLabel = "FILE",
        description = "load RIFL specifications from file (requires GUI and startup file)")
    public @Nullable Path riflFileName = null;

    /**
     * Save all contracts in selected location to automate the creation of multiple
     * ".key"-files
     */
    @Option(names = "--save-all",
        description = "save all selected contracts for automatic execution")
    private boolean isSaveAllContracts = false;

    @Option(names = "--timeout", paramLabel = "INT",
        description = "timeout for each automatic proof of a problem in ms (default: "
            + LemmataAutoModeOptions.DEFAULT_TIMEOUT + ", i.e., no timeout)")
    private int timeout = -1;


    @CommandLine.ArgGroup(
        heading = "Options for justify rules. autoprove taclets (options always with prefix --jr) needs the path to the rule file as argument       The JUSTIFY_RULES option has a number of additional parameters you can set. The following options only apply if --jr-enable is used.")
    private @Nullable LemmataAutoModeOptions justifyRulesOptions;

    @Option(names = { "--verbose", "-v" }, arity = "*", defaultValue = "2")
    private int verbosity = 2;


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

    /**
     * Determines which {@link UserInterfaceControl} is to be used.
     * <p>
     * By specifying <code>AUTO</code> as command line argument this will be set to
     * {@link UiMode#AUTO}, but {@link UiMode#INTERACTIVE} is the default.
     */
    private UiMode uiMode = UiMode.INTERACTIVE;

    /**
     * Determines whether to actually prove or only load a problem when
     * {@link Main#uiMode} is
     * {@link UiMode#AUTO}.
     * <p>
     * This can be controlled from the command line by specifying the argument
     * <code>AUTO_LOADONLY</code> instead of <code>AUTO</code>.
     */
    private boolean loadOnly = false;


    private ProofMacro autoMacro = new SkipMacro();


    /**
     * <p>
     * This flag indicates if the example chooser should be shown if
     * {@link #examplesFolder} is defined (not {@code null}). It is set in the Eclipse integration
     * to {@code false},
     * because it is required to define the path to a different one without showing the chooser.
     * </p>
     * <p>
     * Conclusion: It must be possible to use KeY with a custom examples directory
     * without show in
     * the chooser on startup.
     * </p>
     */
    public boolean showExampleChooserIfExamplesDirIsDefined = true;

    public Main() {
    }

    /**
     * The file names provided on the command line
     */
    @Parameters(arity = "*")
    private List<Path> inputFiles = List.of();

    public static void main(final String[] args) {
        Locale.setDefault(Locale.US);

        // does no harm on non macs
        System.setProperty("apple.laf.useScreenMenuBar", "true");

        Watchdog.start();

        new CommandLine(new Main())
                .execute(args);
    }

    @Override
    public Integer call() throws Exception {
        Debug.ENABLE_DEBUG = debug;

        try {
            // weigl: You can set assertion status via the system class loader,
            // but can not get its current status. Here a workaround.
            assert false;
            LOGGER.info("Assertion evaluation is disabled.");
        } catch (AssertionError e) {
            LOGGER.info("Assertion evaluation is enabled.");
        }

        if (tacletDir != null) {
            System.setProperty(RuleSourceFactory.STD_TACLET_DIR_PROP_KEY,
                tacletDir.toAbsolutePath().toString());
        }

        GeneralSettings.noPruningClosed = isNoPruningClosed;
        GeneralSettings.keepFileRepos = isKeepFileRepos;

        // this property overrides the default
        if (Boolean.getBoolean("key.verbose-ui")) {
            verbosity = Verbosity.TRACE;
        }
        Log.configureLogging(verbosity);
        logInformation();

        if (isExperimental) {
            LOGGER.info("Running in experimental mode ...");
            setEnabledExperimentalFeatures(true);
        } else {
            setEnabledExperimentalFeatures(false);
        }

        preProcessInput();

        printHeader();

        if (showProperties) {
            java.util.Properties props = System.getProperties();
            for (var e : props.entrySet()) {
                LOGGER.info("Property: {} = {}", e.getKey(), e.getValue());
            }
            return 0;
        }

        if (isAuto) {
            uiMode = UiMode.AUTO;
        }

        if (isAutoLoadOnly) {
            uiMode = UiMode.AUTO;
            loadOnly = true;
        }

        if (autoSaveSteps != 0) {
            if (autoSaveSteps < 0) {
                LOGGER.error("Illegal autosave period (--auto-save). Value must be a number >= 0");
                return -1;
            }
            AutoSaver.setDefaultValues(autoSaveSteps, uiMode == UiMode.INTERACTIVE);
        }

        GeneralSettings.disableSpecs = noJmlSpecs;

        if (timeout > 0) {
            LOGGER.info("Timeout is set to {}", timeout);
            ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setTimeout(timeout);
        }

        if (Debug.ENABLE_DEBUG) {
            LOGGER.info("Running in debug mode");
        }

        LOGGER.info("Debug.ENABLE_ASSERTION = {}", Debug.ENABLE_ASSERTION);

        if (riflFileName != null) {
            LOGGER.info("Loading RIFL specification from {}", riflFileName);
            if (!Files.exists(riflFileName)) {
                LOGGER.info("RIFL does not exists {}", riflFileName);
                return 2;
            }
        }

        if (justifyRulesOptions != null) {
            try {
                LemmataHandler handler =
                    new LemmataHandler(justifyRulesOptions, AbstractProfile.getDefaultProfile());
                handler.start();
            } catch (Exception e) {
                LOGGER.error("Lemmata options failed", e);
                return -3;
            }
        }

        if (macro != null) {
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
            if (macro.isEmpty() || autoMacro instanceof SkipMacro) {
                LOGGER.warn("No automatic proof macro specified.");
            }
        }

        AbstractMediatorUserInterfaceControl ui = createUserInterface(inputFiles);

        if (inputFiles.isEmpty()) {
            if (examplesFolder != null
                    && showExampleChooserIfExamplesDirIsDefined
                    && ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                            .getShowLoadExamplesDialog()) {
                ui.openExamples();
            }
        } else {
            ui.setMacro(autoMacro);
            ui.setSaveOnly(isSaveAllContracts);
            for (Path f : inputFiles) {
                ui.loadProblem(f);
            }

            if (ui instanceof ConsoleUserInterfaceControl) {
                return ((ConsoleUserInterfaceControl) ui).allProofsSuccessful ? 0 : 1;
            }
        }

        return 0;
    }

    private void logInformation() {
        LOGGER.debug("Java Version: {}", System.getProperty("java.version"));
        LOGGER.debug("Java Runtime: {}", System.getProperty("java.specification.version"));
        LOGGER.debug("Java VM: {}", System.getProperty("java.vm"));
        LOGGER.debug("OS: {}", System.getProperty("java.os"));
        LOGGER.debug("Hardware: {}", System.getProperty("java.hw"));
        Runtime rt = Runtime.getRuntime();
        LOGGER.info("Memory: total {} MB, max {} MB, free {} MB",
            rt.totalMemory() / 1048576.0,
            rt.maxMemory() / 1048576.0,
            rt.freeMemory() / 1048576.0);
        LOGGER.debug("Available processors: {}", rt.availableProcessors());
    }

    /**
     * Deactivate experimental features.
     */
    public void setEnabledExperimentalFeatures(boolean state) {
        isExperimental = state;
        LOGGER.debug("Experimental Features: {}", state);
        ProofIndependentSettings.DEFAULT_INSTANCE.getFeatureSettings().setActivateAll(state);
    }

    /**
     * Print a header text on to the console.
     */
    private void printHeader() {
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
     * @return a <code>UserInterfaceControl</code> based on the value of
     *         <code>uiMode</code>
     */
    private AbstractMediatorUserInterfaceControl createUserInterface(List<Path> fileArguments) {
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
                // printUsageAndExit(true, "Error: No file to load from.", -4);
                System.exit(-4);
            }

            return new ConsoleUserInterfaceControl(loadOnly);
        } else {
            /*
             * explicitly enable pruning in closed branches for interactive mode (if not* manually
             * disabled)
             */
            MainWindow mainWindow = MainWindow.getInstance();

            if (loadRecentFile) {
                String mostRecent = mainWindow.getRecentFiles().getMostRecent();

                if (mostRecent != null) {
                    File mostRecentFile = new File(mostRecent);
                    if (mostRecentFile.exists()) {
                        fileArguments.add(mostRecentFile.toPath());
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
        Path examplesDir = getExamplesDir() == null
                ? ExampleChooser.lookForExamples()
                : getExamplesDir();

        if (!Files.exists(examplesDir)) {
            examplesDir = setupExamples();
        }
        setExamplesDir(examplesDir.toAbsolutePath());
    }

    private static Path setupExamples() {
        try {
            URL examplesURL = Main.class.getResource("/examples.zip");
            if (examplesURL == null) {
                throw new IOException("Missing examples.zip in resources");
            }

            Path tempDir = createTempDirectory();

            if (tempDir != null) {
                IOUtil.extractZip(examplesURL.openStream(), tempDir);
            }
            return tempDir;
        } catch (IOException e) {
            LOGGER.warn("Error setting up examples", e);
            return null;
        }
    }

    private static Path createTempDirectory() throws IOException {
        Path tempDir = Files.createTempDirectory("keyheap-examples-");
        Runtime.getRuntime().addShutdownHook(new Thread(() -> IOUtil.delete(tempDir.toFile())));
        return tempDir;
    }

    /**
     * Used by {@link de.uka.ilkd.key.gui.KeYFileChooser} (and potentially others)
     * to determine
     * working directory. In case there is at least one location (i.e. a file or
     * directory)
     * specified as command line argument, working directory is determined based on
     * first location
     * that occurred in the list of arguments. Otherwise, value of
     * System.getProperty("user.home")
     * is used to determine working directory.
     *
     * @return {@link File} object representing working directory.
     */
    public static Path getWorkingDir() {
        return workingDir;
    }


    /**
     * Perform necessary actions before loading any problem files. Currently only
     * performs RIFL to JML transformation.
     */
    private void preProcessInput()
            throws ParserException, IOException, ParserConfigurationException, SAXException {
        // RIFL to JML transformation
        if (riflFileName != null) {
            if (inputFiles.isEmpty()) {
                LOGGER.info("[RIFL] No Java file to load from.");
                System.exit(-130826);
            }
            // only use one input file
            Path fileNameOnStartUp = inputFiles.getFirst().toAbsolutePath();
            RIFLTransformer transformer = new RIFLTransformer();
            transformer.doTransform(riflFileName, fileNameOnStartUp,
                RIFLTransformer.getDefaultSavePath(fileNameOnStartUp));
            LOGGER.info("[RIFL] Writing transformed Java files to {}  ...", fileNameOnStartUp);
            inputFiles = transformer.getProblemFiles();
        }

        if (inputFiles != null && !inputFiles.isEmpty()) {
            Path f = inputFiles.getFirst();
            if (Files.isDirectory(f)) {
                workingDir = f;
            } else {
                workingDir = f.getParent();
            }
        } else {
            workingDir = IOUtil.getCurrentDirectory();
        }
    }

    private static Path EXAMPLE_DIR = null;

    public static @Nullable Path getExamplesDir() {
        return EXAMPLE_DIR;
    }

    /**
     * Defines the examples' directory. This method is used by the Eclipse
     * integration (KeY4Eclipse)
     * to use the examples extract from the plug-in into the workspace.
     *
     * @param newExamplesDir The new examples directory to use.
     */
    public static void setExamplesDir(Path newExamplesDir) {
        EXAMPLE_DIR = newExamplesDir;
    }
}
