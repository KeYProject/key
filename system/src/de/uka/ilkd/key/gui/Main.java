// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//


package de.uka.ilkd.key.gui;

import java.io.File;
import java.io.PrintStream;
import java.util.List;

import de.uka.ilkd.key.gui.RecentFileMenu.RecentFileEntry;
import de.uka.ilkd.key.gui.configuration.GeneralSettings;
import de.uka.ilkd.key.gui.configuration.PathConfig;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.gui.lemmatagenerator.LemmataAutoModeOptions;
import de.uka.ilkd.key.gui.lemmatagenerator.LemmataHandler;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.io.AutoSaver;
import de.uka.ilkd.key.ui.BatchMode;
import de.uka.ilkd.key.ui.ConsoleUserInterface;
import de.uka.ilkd.key.ui.UserInterface;
import de.uka.ilkd.key.util.CommandLine;
import de.uka.ilkd.key.util.CommandLineException;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ExperimentalFeature;
import de.uka.ilkd.key.util.KeYResourceManager;
import de.uka.ilkd.key.util.UnicodeHelper;

/**
 * The main entry point for KeY
 *
 * This has been extracted from MainWindow to keep GUI and control further apart.
 */
public final class Main {
/**
 * Command line options
 */
    private static final String HELP = "--help";
    private static final String AUTO = "--auto";
    private static final String LAST = "--last";
    private static final String AUTO_LOADONLY = "--auto-loadonly";
    private static final String AUTOSAVE = "--autosave";
    private static final String EXPERIMENTAL = "--experimental";
    private static final String DEBUG = "--debug";
    private static final String NO_DEBUG = "--no_debug";
    private static final String ASSERTION = "--assertion";
    private static final String NO_ASSERTION = "--no-assertion";
    private static final String NO_JMLSPECS = "--no-jmlspecs";
    public static final String JUSTIFY_RULES ="--justify-rules";
    private static final String PRINT_STATISTICS ="--print-statistics";
    private static final String TIMEOUT ="--timeout";
    private static final String EXAMPLES = "--examples";
    public static final String JKEY_PREFIX = "--jr-";
    public static final String JMAX_RULES = JKEY_PREFIX + "maxRules";
//    deprecated
//    public static final String JPATH_OF_RULE_FILE = JKEY_PREFIX + "pathOfRuleFile";
    public static final String JPATH_OF_RESULT = JKEY_PREFIX + "pathOfResult";
    public static final String JTIMEOUT = JKEY_PREFIX + "timeout";
    public static final String JPRINT = JKEY_PREFIX + "print";
    public static final String JSAVE_RESULTS_TO_FILE = JKEY_PREFIX + "saveProofToFile";
    public static final String JFILE_FOR_AXIOMS = JKEY_PREFIX + "axioms";
    public static final String JFILE_FOR_DEFINITION = JKEY_PREFIX +"signature";
    private static final String VERBOSITY = "--verbose";

    /** The time of the program start in millis. */
    private static long startTime;

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


    public static final String INTERNAL_VERSION =
            KeYResourceManager.getManager().getSHA1();

    public static final String VERSION =
            KeYResourceManager.getManager().getVersion() +
            " (internal: "+INTERNAL_VERSION+")";

    public static final String COPYRIGHT=UnicodeHelper.COPYRIGHT
            +" Copyright 2001"+UnicodeHelper.ENDASH+"2013 "
            +"Karlsruhe Institute of Technology, "
            +"Chalmers University of Technology, and Technische Universit\u00e4t Darmstadt";

    /** Level of verbosity for command line outputs. */
    private static byte verbosity = Verbosity.NORMAL;

    private static String statisticsFile = null;

    private static String examplesDir = null;

    /**
     * Determines which {@link UserInterface} is to be used.
     *
     * By specifying <code>AUTO</code> as command line argument this will be set
     * to {@link UiMode#AUTO}, but {@link UiMode#INTERACTIVE} is the default.
     */
    private static UiMode uiMode = UiMode.INTERACTIVE;

    /**
     * Determines whether to actually prove or only load a problem when
     * {@link Main#uiMode} is {@link UiMode#AUTO}.
     *
     * This can be controlled from the command line by specifying the argument
     * <code>AUTO_LOADONLY</code> instead of <code>AUTO</code>.
     */
    private static boolean loadOnly = false;

    private static String fileNameOnStartUp = null;
    /**
     * Object handling the parsing of commandline options
     */
    private static CommandLine cl;
    /**
     * flag whether recent loaded file should be loaded on startup
     */
    private static boolean loadRecentFile=false;

    /** Lists all features currently marked as experimental.
     * Unless invoked with command line option --experimental ,
     * those will be deactivated.
     */
    private static final ExperimentalFeature[] EXPERIMENTAL_FEATURES =
        {de.uka.ilkd.key.proof.delayedcut.DelayedCut.FEATURE};


    /**
     * <p>
     * This flag indicates if the example chooser should be shown
     * if {@link #examplesDir} is defined (not {@code null}). It is set
     * in the Eclipse integration to {@code false}, because it is required
     * to define the path to a different one without showing the chooser.
     * </p>
     * <p>
     * Conclusion: It must be possible to use KeY with a custom examples
     * directory without show in the chooser on startup.
     * </p>
     */
    public static boolean showExampleChooserIfExamplesDirIsDefined = true;

    public static void main(String[] args) {
        startTime = System.currentTimeMillis();

        // this property overrides the default
        if (Boolean.getBoolean("key.verbose-ui")) verbosity = Verbosity.DEBUG;

        // does no harm on non macs
        System.setProperty("apple.laf.useScreenMenuBar","true");


        try {
            cl = createCommandLine();
            cl.parse(args);
            evaluateOptions(cl);
            UserInterface userInterface = createUserInterface();
            loadCommandLineFile(userInterface);
        } catch (ExceptionInInitializerError e) {
        	System.err.println("D'oh! It seems that KeY was not built properly!");
        	System.exit(777);
        } catch (CommandLineException e) {
            printHeader(); // exception before verbosity option could be read
            if (Debug.ENABLE_DEBUG) {
                e.printStackTrace();
            }
            printUsageAndExit(true, e.getMessage(), -1);
        }

    }

    public static void loadCommandLineFile(UserInterface ui) {
        if (Main.getFileNameOnStartUp() != null) {
            ui.loadProblem(new File(Main.getFileNameOnStartUp()));

        } else if(Main.getExamplesDir() != null && Main.showExampleChooserIfExamplesDirIsDefined) {
            ui.openExamples();
        }
    }

    /**
     * Register commandline options with command line object
     * @return commandline object
     */
    private static CommandLine createCommandLine(){
        CommandLine cl = new CommandLine();
        cl.setIndentation(3);
        cl.addSection("Using KeY");
        cl.addText("Usage: ./runProver [options] [filename]\n\n", false);
        cl.addSection("Options for the KeY-Prover");
        cl.addOption(HELP, null, "display this text");
        cl.addTextPart("--K-help", "display help for technical/debug parameters\n", true);
        cl.addOption(LAST, null, "start prover with last loaded problem (only possible with GUI)");
        cl.addOption(AUTOSAVE, "<number>", "save intermediate proof states each n proof steps to a temporary location (default: 0 = off)");
        cl.addOption(EXPERIMENTAL, null, "switch experimental features on");
        cl.addSection("Batchmode options:");
        cl.addOption(DEBUG, null, "start KeY in debug mode");
        cl.addOption(AUTO, null, "start automatic prove procedure after initialisation without GUI");
        cl.addOption(AUTO_LOADONLY, null, "load files automatically without proving (for testing)");
        cl.addOption(VERBOSITY, "<number>", "verbosity (default: "+Verbosity.NORMAL+")");
        cl.addOption(NO_JMLSPECS, null, "disable parsing JML specifications");
        cl.addOption(EXAMPLES, "<directory>", "load the directory containing the example files on startup");
        cl.addOption(PRINT_STATISTICS, "<filename>",  "output nr. of rule applications and time spent on proving");
        cl.addOption(TIMEOUT, "<timeout>", "timeout for each automatic proof of a problem in ms (default: " + LemmataAutoModeOptions.DEFAULT_TIMEOUT +", i.e., no timeout)");
        cl.addSection("Options for justify rules:");
        cl.addOption(JUSTIFY_RULES, "<filename>", "autoprove taclets (options always with prefix --jr) needs the path to the rule file as argument" );
        cl.addText("\n", true);
        cl.addText("The '" + JUSTIFY_RULES + "' option has a number of additional parameters you can set.", false);
        cl.addText("The following options only apply if '" + JUSTIFY_RULES + "' is used.", false);
        cl.addText("\n", true);
        cl.addOption(JMAX_RULES, "<number>","maximum number of rule application to perform (default: " + LemmataAutoModeOptions.DEFAULT_MAXRULES +")");
        cl.addOption(JPATH_OF_RESULT, "<path>", "store proofs to this folder");
        cl.addOption(JTIMEOUT, "<timeout>", "the timeout for proof of a taclet in ms (default: " + LemmataAutoModeOptions.DEFAULT_TIMEOUT +")");
        cl.addOption(JPRINT, "<terminal/disable>", "send output to terminal or disable output");
        cl.addOption(JSAVE_RESULTS_TO_FILE, "<true/false>", "save or drop proofs (then stored to path given by "+ JPATH_OF_RESULT + ")");
        cl.addOption(JFILE_FOR_AXIOMS, "<filename>", "read axioms from given file");
        cl.addOption(JFILE_FOR_DEFINITION, "<filename>", "read definitions from given file");
        return cl;
    }
    /**
     * Evaluate the parsed commandline options
     * @param commandline object cl
     */
    public static void evaluateOptions(CommandLine cl) {

        if(cl.isSet(VERBOSITY)){ // verbosity
            try {
                verbosity = (byte)cl.getInteger(VERBOSITY, Verbosity.HIGH);
            } catch (CommandLineException e) {
                if(Debug.ENABLE_DEBUG) {
                    e.printStackTrace();
                }
                System.err.println(e.getMessage());
            }
        }

        if (verbosity > Verbosity.SILENT) {
            printHeader();
        }

        if(cl.isSet(AUTO)){
        	uiMode = UiMode.AUTO;
        }
        if(cl.isSet(AUTO_LOADONLY)){
        	uiMode = UiMode.AUTO;
        	loadOnly = true;
        }

        if(cl.isSet(AUTOSAVE)){
            try {
                int eachSteps = cl.getInteger(AUTOSAVE, 0);
                if (eachSteps < 0) {
                    printUsageAndExit(false, "Illegal autosave period (must be a number >= 0)", -5);
                }
                AutoSaver.init(eachSteps, uiMode == UiMode.INTERACTIVE);
            } catch (CommandLineException e) {
                if(Debug.ENABLE_DEBUG) {
                    e.printStackTrace();
                }
                System.err.println(e.getMessage());
            }
        }

        if(cl.isSet(HELP)){
            // 0 as exit value means: no error
            printUsageAndExit(true, null, 0);
        }

        if(cl.isSet(NO_JMLSPECS)){
            GeneralSettings.disableSpecs = true;
        }

        if(cl.isSet(PRINT_STATISTICS)){
            statisticsFile = cl.getString(PRINT_STATISTICS, null);
        }

        if(cl.isSet(TIMEOUT)){
            if (verbosity >= Verbosity.HIGH)
            System.out.println("Timeout is set");
            long timeout = -1;
            try {
                timeout = cl.getLong(TIMEOUT, -1);
                if (verbosity >= Verbosity.HIGH)
                System.out.println("Timeout is: "+ timeout+" ms");
            } catch (CommandLineException e) {
                if(Debug.ENABLE_DEBUG) {
                    e.printStackTrace();
                }
                System.err.println(e.getMessage());
            }

            if (timeout < -1) {
                printUsageAndExit(false, "Illegal timeout (must be a number >= -1)", -5);
            }

            ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setTimeout(timeout);
        }

        if(cl.isSet(EXAMPLES)){
            examplesDir = cl.getString(EXAMPLES, null);
        }

        if (verbosity > Verbosity.SILENT) {
        if (Debug.ENABLE_DEBUG) {
            System.out.println("Running in debug mode ...");
        }

        if (Debug.ENABLE_ASSERTION) {
            System.out.println("Using assertions ...");
        } else {
            System.out.println("Not using assertions ...");
        }
        }

        if(cl.isSet(EXPERIMENTAL)){
            if (verbosity > Verbosity.SILENT)
            System.out.println("Running in experimental mode ...");
        } else {
            deactivateExperimentalFeatures();
        }

        if(cl.isSet(LAST)){
            loadRecentFile=true;
        }

        List<String> fileArguments = cl.getArguments();

        if (cl.isSet(JUSTIFY_RULES)) {
            evaluateLemmataOptions(cl);
        }

        if (cl.isSet(DEBUG)) {
            Debug.ENABLE_DEBUG = true;
        }

        //arguments not assigned to a command line option may be files

        if(!fileArguments.isEmpty()){
            String fileArg = fileArguments.get(0);
            if(new File(fileArg).exists()) {
                fileNameOnStartUp = fileArg;
            } else {
                printUsageAndExit(false, "File not found: " + fileArg, -4);
            }
        }

    }

    /** Deactivate experimental features. */
    private static void deactivateExperimentalFeatures () {
        for (ExperimentalFeature feature: EXPERIMENTAL_FEATURES)
            feature.deactivate();
    }


    /** Print a header text on to the console. */
    private static void printHeader() {
        System.out.println("\nKeY Version " + VERSION);
        System.out.println(COPYRIGHT + "\nKeY is protected by the " +
                "GNU General Public License\n");
    }

    /**
     * Initializes the {@link UserInterface} to be used by KeY.
     *
     * {@link ConsoleUserInterface} will be used if {@link Main#uiMode} is
     * {@link UiMode#AUTO} and {@link WindowUserInterface} otherwise.
     *
     * @return a <code>UserInterface</code> based on the value of
     *         <code>uiMode</code>
     */
    private static UserInterface createUserInterface() {
        UserInterface ui;

        if (uiMode == UiMode.AUTO) {
            // terminate immediately when an uncaught exception occurs (e.g., OutOfMemoryError), see bug #1216
            Thread.setDefaultUncaughtExceptionHandler(new Thread.UncaughtExceptionHandler() {
                @Override
                public void uncaughtException(Thread t, Throwable e) {
                    if (verbosity > Verbosity.SILENT) {
                        System.out.println("Auto mode was terminated by an exception:"+e.getClass().toString().substring(5));
                        if (verbosity >= Verbosity.DEBUG) e.printStackTrace();
                        final String msg = e.getMessage();
                        if (msg!=null) System.out.println(msg);
                    }
                    System.exit(-1);
                }
            });
            if (fileNameOnStartUp == null)
                printUsageAndExit(true, "Error: No file to load from.", -4);
            BatchMode batch = new BatchMode(fileNameOnStartUp, loadOnly);

            ui = new ConsoleUserInterface(batch, true, verbosity);
        } else {
            updateSplashScreen();
            MainWindow mainWindow = MainWindow.getInstance();

            if (loadRecentFile) {
                RecentFileEntry mostRecent =
                        mainWindow.getRecentFiles().getMostRecent();

                if (mostRecent != null) {
                    fileNameOnStartUp = mostRecent.getAbsolutePath();
                }
            }

            ui = mainWindow.getUserInterface();
	    if (fileNameOnStartUp != null && verbosity > Verbosity.SILENT)
	        System.out.println("Loading: "+fileNameOnStartUp);
        }

        return ui;

    }

    private static void updateSplashScreen() {
        try {
            final java.awt.SplashScreen sp = java.awt.SplashScreen.getSplashScreen();
            if (sp == null) return;
            // insert customization code here
            // see http://docs.oracle.com/javase/tutorial/uiswing/misc/splashscreen.html
        } catch (Exception e) {}
    }

    private static void evaluateLemmataOptions(CommandLine options){

        LemmataAutoModeOptions opt;
        try {

            opt = new LemmataAutoModeOptions(options, INTERNAL_VERSION,
                    PathConfig.getKeyConfigDir());
            LemmataHandler handler = new LemmataHandler(opt,
                    AbstractProfile.getDefaultProfile());
            handler.start();

        } catch(Exception e) {
            if(Debug.ENABLE_DEBUG) {
                e.printStackTrace();
            }
            printUsageAndExit(false, e.getMessage(), -2);
        }

    }

    private static void printUsageAndExit(boolean printUsage, String offending, int exitValue) {
        PrintStream ps = exitValue==0 ? System.out : System.err;
        if(offending != null) {
            ps.println(offending);
        }
        if (printUsage) {
            cl.printUsage(ps);
        }
        System.exit(exitValue);
    }

    public static String getExamplesDir() {
        return examplesDir;
    }

    /**
     * Defines the examples directory. This method is used by the
     * Eclipse integration (KeY4Eclipse) to use the examples extract
     * from the plug-in into the workspace.
     * @param newExamplesDir The new examples directory to use.
     */
    public static void setExamplesDir(String newExamplesDir) {
        examplesDir = newExamplesDir;
    }

    /**
     * @return the statisticsFile
     */
    public static String getStatisticsFile() {
        return statisticsFile;
    }

    /**
     * @return the fileNameOnStartUp
     */
    public static String getFileNameOnStartUp() {
        return fileNameOnStartUp;
    }

    /** Returns the time of the program start in millis. */
    public static long getStartTime() {
        return startTime;
    }

    /** Command line output verbosity levels. */
    public static final class Verbosity {
        public static final byte SILENT = 0;
        public static final byte NORMAL = 1;
        public static final byte HIGH = 2;
        public static final byte DEBUG = 4;
    }
}
