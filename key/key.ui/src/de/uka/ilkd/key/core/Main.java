// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.core;

import java.awt.Desktop;
import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;

import org.key_project.util.java.IOUtil;
import org.key_project.util.reflection.ClassLoaderUtil;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.gui.ExampleChooser;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.RecentFileMenu.RecentFileEntry;
import de.uka.ilkd.key.gui.WindowUserInterfaceControl;
import de.uka.ilkd.key.gui.join.JoinMenuItem;
import de.uka.ilkd.key.gui.joinrule.JoinRuleMenuItem;
import de.uka.ilkd.key.gui.lemmatagenerator.LemmataAutoModeOptions;
import de.uka.ilkd.key.gui.lemmatagenerator.LemmataHandler;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.SkipMacro;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.io.AutoSaver;
import de.uka.ilkd.key.proof.io.RuleSourceFactory;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.settings.PathConfig;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.ui.AbstractMediatorUserInterfaceControl;
import de.uka.ilkd.key.ui.ConsoleUserInterfaceControl;
import de.uka.ilkd.key.ui.Verbosity;
import de.uka.ilkd.key.util.CommandLine;
import de.uka.ilkd.key.util.CommandLineException;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ExperimentalFeature;
import de.uka.ilkd.key.util.KeYConstants;
import de.uka.ilkd.key.util.KeYResourceManager;
import de.uka.ilkd.key.util.UnicodeHelper;
import de.uka.ilkd.key.util.rifl.RIFLTransformer;

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
    private static final String SHOW_PROPERTIES = "--show-properties";
    private static final String AUTO = "--auto";
    private static final String LAST = "--last";
    private static final String AUTO_LOADONLY = "--auto-loadonly";
    private static final String AUTOSAVE = "--autosave";
    private static final String EXPERIMENTAL = "--experimental";
    private static final String DEBUG = "--debug";
    private static final String MACRO = "--macro";
    private static final String NO_JMLSPECS = "--no-jmlspecs";
    private static final String TACLET_DIR = "--tacletDir";
    public static final String JUSTIFY_RULES ="--justify-rules";
    private static final String SAVE_ALL_CONTRACTS = "--save-all";
    private static final String TIMEOUT ="--timeout";
    private static final String EXAMPLES = "--examples";
    private static final String RIFL = "--rifl";
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
    
    /**
     * The {@link KeYDesktop} used by KeY. The default implementation is
     * replaced in Eclipse. For this reason the {@link Desktop} should never
     * be used directly.
     */
    private static KeYDesktop keyDesktop = new DefaultKeYDesktop();

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

    /** Level of verbosity for command line outputs. */
    private static byte verbosity = Verbosity.NORMAL;

    private static String examplesDir = null;

    /**
     * Determines which {@link UserInterfaceControl} is to be used.
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

    /**
     * Object handling the parsing of commandline options
     */
    private static CommandLine cl;
    /**
     * flag whether recent loaded file should be loaded on startup
     */
    private static boolean loadRecentFile=false;
    
    /**
     * The file names provided on the command line
     */
    private static List<File> fileArguments;

    /**
     * Lists all features currently marked as experimental. Unless invoked with
     * command line option --experimental , those will be deactivated.
     */
    private static final ExperimentalFeature[] EXPERIMENTAL_FEATURES = {
            JoinMenuItem.FEATURE, JoinRuleMenuItem.FEATURE };

    /**
     * Path to a RIFL specification file.
     */
    private static String riflFileName = null;

    /**
     * Save all contracts in selected location to automate the creation
     * of multiple ".key"-files
     */
    private static boolean saveAllContracts = false;

    private static ProofMacro autoMacro = new SkipMacro();

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

    public static void main(final String[] args) {
        // this property overrides the default
        if (Boolean.getBoolean("key.verbose-ui")) {
            verbosity = Verbosity.DEBUG;
        }

        // does no harm on non macs        
        System.setProperty("apple.laf.useScreenMenuBar","true");

        try {
            cl = createCommandLine();
            cl.parse(args);
            evaluateOptions(cl);
            fileArguments = cl.getFileArguments();
            AbstractMediatorUserInterfaceControl userInterface = createUserInterface(fileArguments);
            fileArguments = preProcessInput(fileArguments);
            loadCommandLineFiles(userInterface, fileArguments);
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

    public static void loadCommandLineFiles(AbstractMediatorUserInterfaceControl ui, List<File> fileArguments) {
        if (!fileArguments.isEmpty()) {
            ui.setMacro(autoMacro);
            ui.setSaveOnly(saveAllContracts);
            for (int i = 0; i < fileArguments.size(); i++) {
                File f = fileArguments.get(i);
                ui.loadProblem(f);
            }
            if (ui instanceof ConsoleUserInterfaceControl) {
                System.exit(((ConsoleUserInterfaceControl) ui).allProofsSuccessful ? 0 : 1);
            }
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
        cl.addText("Usage: ./key [options] [filename]\n\n", false);
        cl.addSection("Options for the KeY-Prover");
        cl.addOption(HELP, null, "display this text");
        cl.addTextPart("--K-help", "display help for technical/debug parameters\n", true);
        cl.addOption(SHOW_PROPERTIES, null, "list all Java properties and exit");
        cl.addOption(LAST, null, "start prover with last loaded problem (only possible with GUI)");
        cl.addOption(AUTOSAVE, "<number>", "save intermediate proof states each n proof steps to a temporary location (default: 0 = off)");
        cl.addOption(EXPERIMENTAL, null, "switch experimental features on");
        cl.addSection("Batchmode options:");
        cl.addOption(TACLET_DIR, "<dir>", "load base taclets from a directory, not from internal structures");
        cl.addOption(DEBUG, null, "start KeY in debug mode");
        cl.addOption(AUTO, null, "start automatic prove procedure after initialisation without GUI");
        cl.addOption(AUTO_LOADONLY, null, "load files automatically without proving (for testing)");
        cl.addOption(VERBOSITY, "<number>", "verbosity (default: "+Verbosity.NORMAL+")");
        cl.addOption(NO_JMLSPECS, null, "disable parsing JML specifications");
        cl.addOption(EXAMPLES, "<directory>", "load the directory containing the example files on startup");
        cl.addOption(RIFL, "<filename>", "load RIFL specifications from file (requires GUI and startup file)");
        cl.addOption(MACRO, "<proofMacro>", "apply automatic proof macro");
        cl.addOption(SAVE_ALL_CONTRACTS, null, "save all selected contracts for automatic execution");
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
        
        if (cl.isSet(SHOW_PROPERTIES)) {
            try {
                java.util.Properties props = System.getProperties();
                for (Object o: props.keySet()) {
                    System.out.println(""+o+"=\""+props.get(o)+"\"");
                }
            } finally {
                System.exit(0);
            }
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
                AutoSaver.setDefaultValues(eachSteps, uiMode == UiMode.INTERACTIVE);
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

        if(cl.isSet(TIMEOUT)){
            if (verbosity >= Verbosity.HIGH) {
            System.out.println("Timeout is set");
            }
            long timeout = -1;
            try {
                timeout = cl.getLong(TIMEOUT, -1);
                if (verbosity >= Verbosity.HIGH) {
                System.out.println("Timeout is: "+ timeout+" ms");
                }
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

        if (cl.isSet(EXPERIMENTAL)) {
            if (verbosity > Verbosity.SILENT) {
            System.out.println("Running in experimental mode ...");
            }
            setEnabledExperimentalFeatures(true);
        } else {
            setEnabledExperimentalFeatures(false);
        }

        if (cl.isSet(RIFL)) {
            riflFileName = cl.getString(RIFL, null);
            if (verbosity > Verbosity.SILENT) {
                System.out.println("[RIFL] Loading RIFL specification from "+riflFileName+ " ...");
            }
        }

        if(cl.isSet(LAST)){
            loadRecentFile=true;
        }

        if (cl.isSet(JUSTIFY_RULES)) {
            evaluateLemmataOptions(cl);
        }

        if (cl.isSet(DEBUG)) {
            Debug.ENABLE_DEBUG = true;
        }

        if (cl.isSet(MACRO)) {
            String macro = cl.getString(MACRO, "");
            for (ProofMacro m: ClassLoaderUtil.loadServices(ProofMacro.class)) {
                if (macro.equals(m.getClass().getSimpleName())) {
                    // memorize macro for later
                    try {
                        autoMacro = m.getClass().newInstance();
                    } catch (InstantiationException e) {
                        System.err.println("Automatic proof macro can not be instantiated!");
                        e.printStackTrace();
                    } catch (IllegalAccessException e) {
                        System.err.println("Automatic proof macro can not be accessed!");
                        e.printStackTrace();
                    }
                    break;
                }
            }
            if (macro.equals("") || autoMacro instanceof SkipMacro) {
                System.err.println("No automatic proof macro specified.");
            }
        }

        if (cl.isSet(SAVE_ALL_CONTRACTS)) {
            saveAllContracts = true;
        }

        if(cl.isSet(TACLET_DIR)) {
            System.setProperty(RuleSourceFactory.STD_TACLET_DIR_PROP_KEY,
                    cl.getString(TACLET_DIR, ""));
        }

    }

    /** Deactivate experimental features. */
    public static void setEnabledExperimentalFeatures (boolean state) {
        if(state) {
            for (ExperimentalFeature feature: EXPERIMENTAL_FEATURES) {
                feature.activate();
            }
        } else {
        for (ExperimentalFeature feature: EXPERIMENTAL_FEATURES) {
            feature.deactivate();
    }
    }
    }


    /** Print a header text on to the console. */
    private static void printHeader() {
        System.out.println("\nKeY Version " + KeYConstants.VERSION);
        System.out.println(KeYConstants.COPYRIGHT + "\nKeY is protected by the " +
                "GNU General Public License\n");
    }

    /**
     * Initializes the {@link UserInterfaceControl} to be used by KeY.
     *
     * {@link ConsoleUserInterfaceControl} will be used if {@link Main#uiMode} is
     * {@link UiMode#AUTO} and {@link WindowUserInterfaceControl} otherwise.
     *
     * @return a <code>UserInterfaceControl</code> based on the value of
     *         <code>uiMode</code>
     */
    private static AbstractMediatorUserInterfaceControl createUserInterface(List<File> fileArguments) {

        if (uiMode == UiMode.AUTO) {
            // terminate immediately when an uncaught exception occurs (e.g., OutOfMemoryError), see bug #1216
            Thread.setDefaultUncaughtExceptionHandler(new Thread.UncaughtExceptionHandler() {
                @Override
                public void uncaughtException(Thread t, Throwable e) {
                    if (verbosity > Verbosity.SILENT) {
                        System.out.println("Auto mode was terminated by an exception:"
                                            + e.getClass().toString().substring(5));
                        if (verbosity >= Verbosity.DEBUG) {
                            e.printStackTrace();
                        }
                        final String msg = e.getMessage();
                        if (msg!=null) {
                            System.out.println(msg);
                        }
                    }
                    System.exit(-1);
                }
            });
            if (fileArguments.isEmpty()) {
                printUsageAndExit(true, "Error: No file to load from.", -4);
            }

            return new ConsoleUserInterfaceControl(verbosity, loadOnly);
        } else {
            updateSplashScreen();
            MainWindow mainWindow = MainWindow.getInstance();
            
            if (loadRecentFile) {
                RecentFileEntry mostRecent =
                        mainWindow.getRecentFiles().getMostRecent();

                if (mostRecent != null) {
                    File mostRecentFile = new File(mostRecent.getAbsolutePath());
                    if (mostRecentFile.exists()) {
                        fileArguments.add(mostRecentFile);
                    } else {
                        System.out.println("File does not exist anymore: " + mostRecentFile.toString());
                    }
                }
            }
            ensureExamplesAvailable();
            return mainWindow.getUserInterface();
        }

    }
    
    public static void ensureExamplesAvailable() {
       File examplesDir = getExamplesDir() == null ? 
                          ExampleChooser.lookForExamples() : 
                          new File(getExamplesDir());
       if (!examplesDir.exists()) {
          setExamplesDir(WebstartMain.setupExamples().getAbsolutePath());
       }
    }

    private static void updateSplashScreen() {
        try {
            final java.awt.SplashScreen sp = java.awt.SplashScreen.getSplashScreen();
            if (sp == null)
             {
                return;
            // insert customization code here
            // see http://docs.oracle.com/javase/tutorial/uiswing/misc/splashscreen.html
            }
        } catch (Exception e) {}
    }

    private static void evaluateLemmataOptions(CommandLine options){

        LemmataAutoModeOptions opt;
        try {

            opt = new LemmataAutoModeOptions(options, KeYConstants.INTERNAL_VERSION,
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

    public static void printUsageAndExit(boolean printUsage, String offending, int exitValue) {
        PrintStream ps = exitValue==0 ? System.out : System.err;
        if(offending != null) {
            ps.println(offending);
        }
        if (printUsage) {
            cl.printUsage(ps);
        }
        System.exit(exitValue);
    }

    /**
     * Used by {@link de.uka.ilkd.key.gui.KeYFileChooser} (and potentially
     * others) to determine working directory. In case there is at least one
     * location (i.e. a file or directory) specified as command line argument,
     * working directory is determined based on first location that occurred in
     * the list of arguments. Otherwise, value of System.getProperty("user.home")
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
     * Perform necessary actions before loading any problem files.
     * Currently only performs RIFL to JML transformation.
     */
    private static List<File> preProcessInput (List<File> filesOnStartup) {
        List<File> result = new ArrayList<File>();
        // RIFL to JML transformation
        if (riflFileName != null) {
            if (filesOnStartup.isEmpty()) {
                System.out.println("[RIFL] No Java file to load from.");
                System.exit (-130826);
            }
            // only use one input file
            String fileNameOnStartUp = null;
			try {
				fileNameOnStartUp = filesOnStartup.get(0).getCanonicalPath();
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
//            final KeYRecoderExceptionHandler kexh = ui.getMediator().getExceptionHandler();
            RIFLTransformer.transform(riflFileName, fileNameOnStartUp);
            fileNameOnStartUp = RIFLTransformer.getDefaultSavePath(fileNameOnStartUp);
            if (verbosity > Verbosity.SILENT)
                System.out.println("[RIFL] Writing transformed Java files to "+fileNameOnStartUp+" ...");
            result.add(new File(fileNameOnStartUp));
        }
        return result;
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
     * Returns the {@link KeYDesktop} to use. Never use {@link Desktop}
     * directly because the {@link KeYDesktop} is different in Eclipse.
     * @return The {@link KeYDesktop} to use.
     */
    public static KeYDesktop getKeyDesktop() {
        return keyDesktop;
    }

    /**
     * Sets the {@link KeYDesktop} to use.
     * @param keyDesktop The new {@link KeYDesktop} to use.
     */
    public static void setKeyDesktop(KeYDesktop keyDesktop) {
        assert keyDesktop != null;
        Main.keyDesktop = keyDesktop;
    }
}
