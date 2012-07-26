package de.uka.ilkd.key.gui;

import java.io.File;
import java.io.IOException;
import java.util.LinkedList;

import de.uka.ilkd.key.gui.configuration.GeneralSettings;
import de.uka.ilkd.key.gui.configuration.PathConfig;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.gui.lemmatagenerator.LemmataAutoModeOptions;
import de.uka.ilkd.key.gui.lemmatagenerator.LemmataHandler;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.ui.BatchMode;
import de.uka.ilkd.key.ui.ConsoleUserInterface;
import de.uka.ilkd.key.ui.UserInterface;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.GuiUtilities;
import de.uka.ilkd.key.util.KeYResourceManager;

/**
 * The main entry point for KeY
 * 
 * This has been extracted from MainWindow to keep GUI and control further apart.
 */
public class Main {

    public static final String INTERNAL_VERSION = 
        KeYResourceManager.getManager().getSHA1();

    public static final String VERSION = 
        KeYResourceManager.getManager().getVersion() + 
        " (internal: "+INTERNAL_VERSION+")";

    public static final String COPYRIGHT="(C) Copyright 2001-2011 "
        +"Universit\u00e4t Karlsruhe, Universit\u00e4t Koblenz-Landau, "
        +"and Chalmers University of Technology";


    private static final boolean VERBOSE_UI = Boolean.getBoolean("key.verbose-ui");
        
    private static String statisticsFile = null;

    private static String examplesDir = null;


    private static String fileNameOnStartUp = null;
    /**
     * <p>
     * This flag indicates if the example chooser should be shown
     * if {@link #examplesDir} is defined (not {@code null}). It is set
     * in the Eclipse integration to {@code false}, because it is required
     * to define the path to a different one without showing the chooser.
     * </p>
     * <p>
     * Conclusion: It must be possible to use KeY with a custom examples
     * directory without showin the chooser on startup.
     * </p>
     */
    public static boolean showExampleChooserIfExamplesDirIsDefined = true;
    
    public static void main(String[] args) {
        System.out.println("\nKeY Version " + VERSION);
        System.out.println(COPYRIGHT + "\nKeY is protected by the " +
        "GNU General Public License\n");

        // does no harm on non macs
        System.setProperty("apple.laf.useScreenMenuBar","true");

        UserInterface userInterface = evaluateOptions(args);

        loadCommandLineFile(userInterface);        
    }
    
    public static void loadCommandLineFile(UserInterface ui) {
        if (Main.getFileNameOnStartUp() != null) {
            ui.loadProblem(new File(Main.getFileNameOnStartUp()));
        } else if(Main.getExamplesDir() != null && Main.showExampleChooserIfExamplesDirIsDefined) {
            ui.openExamples();
        }
    }

    public static UserInterface evaluateOptions(String[] opt) {
        UserInterface ui = null;
    	int index = 0;
        ProofSettings.DEFAULT_SETTINGS.setProfile(new JavaProfile());
        String uiMode = "INTERACTIVE";
        while (opt.length > index) {
            if ((new File(opt[index])).exists()) {
                fileNameOnStartUp=opt[index];
            } else {
                opt[index] = opt[index].toUpperCase();
				if (opt[index].equals("NO_DEBUG")) {
                    de.uka.ilkd.key.util.Debug.ENABLE_DEBUG = false;
                } else if (opt[index].equals("DEBUG")) {
                    de.uka.ilkd.key.util.Debug.ENABLE_DEBUG = true;
                } else if (opt[index].equals("NO_ASSERTION")) {
                    de.uka.ilkd.key.util.Debug.ENABLE_ASSERTION = false;
                } else if (opt[index].equals("ASSERTION")) {
                    de.uka.ilkd.key.util.Debug.ENABLE_ASSERTION = true;
                } else if (opt[index].equals("NO_JMLSPECS")) {
                    GeneralSettings.disableSpecs = true;
                } else if (opt[index].equals("JUSTIFYRULES")){
                    LinkedList<String> options = new LinkedList<String>();
                    for(int i = index+1; i < opt.length; i++){
                        options.add(opt[i]);
                    }
                    evaluateLemmataOptions(options);
                    // is last option 
                    break; 
                } else if (opt[index].startsWith("AUTO")) {
                        uiMode = opt[index];
				} else if (opt[index].equals("TIMEOUT")) {
                    long timeout = -1;
                    try {
                        timeout = Long.parseLong(opt[index + 1]);
                    } catch (NumberFormatException nfe) {
                        System.out.println("Illegal timeout (must be a number >=-1).");
                        System.exit(-1);
                    }
                    if (timeout < -1) {
                        System.out.println("Illegal timeout (must be a number >=-1).");
                        System.exit(-1);                        
                    }
                    index++;                   
                    ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setTimeout(timeout);
                } else if (opt[index].equals("PRINT_STATISTICS")) {                     
                    if ( !( opt.length > index + 1 ) ) printUsageAndExit ();
                    statisticsFile = opt[++index];
                } else if(opt[index].equals("EXAMPLES")) {
                    if ( !( opt.length > index + 1 ) ) printUsageAndExit ();
                    examplesDir = opt[++index];
                } else {
                    printUsageAndExit ();
                }		
            }

            index++;
        }	
        if (Debug.ENABLE_DEBUG) {
            System.out.println("Running in debug mode ...");
        } else {
            System.out.println("Running in normal mode ...");
        }
        if (Debug.ENABLE_ASSERTION) {
            System.out.println("Using assertions ...");	   
        } else {
        	System.out.println("Not using assertions ...");	   
        }
        
        if (uiMode.startsWith("AUTO")) {
        	BatchMode batch = new BatchMode(fileNameOnStartUp, 
        		uiMode.equals("AUTO_LOADONLY"));            
        	ui = new ConsoleUserInterface(batch, VERBOSE_UI);
        } else {
        	GuiUtilities.invokeAndWait(new Runnable() {
        		public void run() {
        			MainWindow key = MainWindow.getInstance();
        			key.setVisible(true);
        		}
        	});    
        	ui = MainWindow.getInstance().getUserInterface();
        }
        return ui;
    }    

    private static void evaluateLemmataOptions(LinkedList<String> options){
        LemmataAutoModeOptions opt;
        try {

            opt = new LemmataAutoModeOptions(options, INTERNAL_VERSION, 
                    PathConfig.getKeyConfigDir());
            
        } catch(Exception e) {
            System.out.println("An error occured while reading the lemma parameters:");
            System.out.println(e.getMessage());
            e.printStackTrace();
            System.exit(1);
            return;
        }
        
        
        try {
            LemmataHandler handler = new LemmataHandler(opt,
                    ProofSettings.DEFAULT_SETTINGS.getProfile());
            handler.start();
        }
        catch(ProofInputException exception){
            System.out.println("Could not create dummy file: " + exception);
        }
        catch(IOException exception){
            System.out.println("Could not create dummy file: " + exception);
        }

    }

    private static void printUsageAndExit() {
        System.out.println("File not found or unrecognized option.\n");
        System.out.println("Possible parameters are (* = default): ");
        System.out.println("  no_debug        : disables debug mode (*)");
        System.out.println("  debug           : enables debug mode");
        System.out.println("  no_assertion    : disables assertions");
        System.out.println("  assertion       : enables assertions (*)");
        System.out.println("  no_jmlspecs     : disables parsing JML specifications");
        System.out.println("  auto	      : start prove procedure after initialisation");
        System.out.println("  print_statistics <filename>" );
        System.out.println("                  : in auto mode, output nr. of rule applications and time spent");
        System.out.println("  timeout <time in ms>");
        System.out.println("                  : set maximal time for rule " +
                            "application in ms (-1 disables timeout)");
        System.out.println("  <filename>      : loads a .key file");
        System.exit(-1);
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
}
