// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.gui;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

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
import de.uka.ilkd.key.util.CommandLineException;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.GuiUtilities;
import de.uka.ilkd.key.util.KeYResourceManager;
import de.uka.ilkd.key.util.CommandLine;

/**
 * The main entry point for KeY
 *
 * This has been extracted from MainWindow to keep GUI and control further apart.
 */
public class Main {
    private static final String HELP = "--help";
    private static final String AUTO = "--auto";
    private static final String LAST = "--last";
    private static final String AUTO_LOADONLY = "--auto_loadonly";
    private static final String EXPERIMENTAL = "--experimental";
    private static final String DEBUG = "--debug";
    private static final String NO_DEBUG = "--no_debug";
    private static final String ASSERTION = "--assertion";
    private static final String NO_ASSERTION = "--no_assertion";
    private static final String NO_JMLSPECS = "--no_jmlspecs";
    public static final String JUSTIFY_RULES ="--justify_rules";
    private static final String PRINT_STATISTICS ="--print_statistics";
    private static final String TIMEOUT ="--timeout";
    private static final String EXAMPLES = "--examples"; 
    public static final String JKEY_PREFIX = "--jr-";
    public static final String JMAX_RULES = JKEY_PREFIX + "maxRules";
    public static final String JPATH_OF_RULE_FILE = JKEY_PREFIX + "pathOfRuleFile";
    public static final String JPATH_OF_RESULT = JKEY_PREFIX + "pathOfResult";
    public static final String JTIMEOUT = JKEY_PREFIX + "timeout";
    public static final String JPRINT = JKEY_PREFIX + "print";
    public static final String JSAVE_RESULTS_TO_FILE = JKEY_PREFIX + "saveProofToFile";
    public static final String JFILE_FOR_AXIOMS = JKEY_PREFIX + "axioms";
    public static final String JFILE_FOR_DEFINITION = JKEY_PREFIX +"signature";
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
    private static CommandLine cl;


    
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
    
        System.out.println("\nKeY Version " + VERSION);
        System.out.println(COPYRIGHT + "\nKeY is protected by the " +
                "GNU General Public License\n");

        // does no harm on non macs
        System.setProperty("apple.laf.useScreenMenuBar","true");

        try {
			cl = createCommandLine();
			cl.parse(args);
			UserInterface userInterface = evaluateOptions(cl);
			loadCommandLineFile(userInterface);
		} catch (CommandLineException e) {
			e.printStackTrace();
			System.out.println("Exception during parsing of commandline options");
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
     * Returns the used title. This information is required in other
     * projects which instantiates the {@link MainWindow} manually.
     * @return The title of {@link MainWindow} to use.
     */
    public static String getMainWindowTitle() {
        return "KeY " + KeYResourceManager.getManager().getVersion();
    }
    private static CommandLine createCommandLine(){
    	CommandLine cl= new CommandLine();
    	cl.setIndentation(3);
    	cl.addText("./runProver [options | --justify_rules [justify rule options] filename] [filename(s)]\n\n", false);
    	cl.addText("Options for the KeY-Prover\n", false);
    	cl.addText("\n", false);
    	cl.addOption(HELP, null, "display this text");
    	cl.addTextPart("--Khelp", "display help for technical/debug parameters\n", true);
    	cl.addOption(LAST, null, "start prover with last loaded problem (only possible with GUI)");
    	cl.addOption(EXPERIMENTAL, null, "switch experimental features on");
    	cl.addText("Batchmode options:\n", false);
    	cl.addOption(AUTO, null, "start automatic prove procedure after initialisation without GUI");
    	cl.addOption(AUTO_LOADONLY, null, "load files automatically without proving (for testing)");
    	cl.addOption(NO_JMLSPECS, null, "disable parsing JML specifications");
    	cl.addOption(EXAMPLES, "<directory>", "load the directory containing the example files on startup");
    	cl.addOption(PRINT_STATISTICS, "<filename>",  "output nr. of rule applications and time spent on proving");
    	cl.addOption(TIMEOUT, "<timeout>", "timeout for each automatic proof of a problem in ms (default: " + LemmataAutoModeOptions.DEFAULT_TIMEOUT +", i.e., no timeout)");
    	cl.addText("Options for justify rules:\n", false);
    	cl.addOption(JUSTIFY_RULES, "<filename>", "autoprove taclets (options always with prefix --jr) needs the path to the rule file as argument" );
    	cl.addText("\n", true);
    	cl.addText("The 'justifyrules' command has a number of options you can set. As default configuration the proofs are not stored to a file.\n", false);
    	cl.addText("Provide the option name and the value as separate arguments.\n", false);
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
    public static UserInterface evaluateOptions(CommandLine cl) {
        UserInterface ui = null;
        ProofSettings.DEFAULT_SETTINGS.setProfile(new JavaProfile());
        String uiMode = "INTERACTIVE";
        
        if(cl.isSet(AUTO)){
        	uiMode="AUTO";
        }
        if(cl.isSet(AUTO_LOADONLY)){
        	uiMode="AUTO_LOADONLY";
        }
        
        if(cl.isSet(HELP)){
        	printUsageAndExit(false, null);	
        }
//        if(cl.isSet(DEBUG)){
//        	 de.uka.ilkd.key.util.Debug.ENABLE_DEBUG = true;
//        }
//        if(cl.isSet(NO_DEBUG)){
//        	de.uka.ilkd.key.util.Debug.ENABLE_DEBUG = false;
//        }
//        if(cl.isSet(ASSERTION)){
//        	de.uka.ilkd.key.util.Debug.ENABLE_ASSERTION = true;
//        }
//        if(cl.isSet(NO_ASSERTION)){
//        	de.uka.ilkd.key.util.Debug.ENABLE_ASSERTION = false;
//        }
        if(cl.isSet(NO_JMLSPECS)){
        	GeneralSettings.disableSpecs = true;
        }

        if(cl.isSet(PRINT_STATISTICS)){
        	statisticsFile = cl.getString(PRINT_STATISTICS, null);
        	if(statisticsFile.equals(null)){
        		printUsageAndExit(true,null);
        	}
        }
        if(cl.isSet(TIMEOUT)){
           System.out.println("Timeout is set");
           long timeout = -1;
           try {
               timeout = cl.getLong(TIMEOUT, -1);
               System.out.println("Timeout is: "+ timeout);
           } catch (NumberFormatException nfe) {
               System.out.println("Illegal timeout (must be a number >=-1).");
               System.exit(-1);
           } catch (CommandLineException e) {
        	   System.out.println("Wrong argument for timeout");
		   }
           if (timeout < -1) {
               System.out.println("Illegal timeout (must be a number >=-1).");
               System.exit(-1);
           }
           ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setTimeout(timeout);
        }
        if(cl.isSet(EXAMPLES)){
        	examplesDir = cl.getString(EXAMPLES, null);
        	if (examplesDir.equals(null)){
        		printUsageAndExit(true, null);
        	}
        }
        
     	List<String> fileArguments = cl.getArguments();
     	Iterator iter = fileArguments.iterator();
//     	for (String string : fileArguments) {
//			System.out.println("Hier:"+string);
//		}
     	//-jr-
        if(cl.isSet(JUSTIFY_RULES))
        {evaluateLemmataOptions(cl);}
        
        //arguments not assigned to a command line option may be files

      	if(!fileArguments.isEmpty()){
      		if(new File(fileArguments.get(0)).exists()){
      			System.out.println(fileArguments.get(0));
      			fileNameOnStartUp=fileArguments.get(0);    	
      		}
      	}

        
//        while (opt.length > index) loop:{
//            if ((new File(opt[index])).exists()) {
//                fileNameOnStartUp=opt[index];
//            } else  { // long option 
//                try {
//                    String option = opt[index].toUpperCase();
//                    CommandLineOption clo = CommandLineOption.valueOf(option);
//                    switch (clo) {
//                    case AUTO:
//                    case AUTO_LOADONLY:
//                        uiMode = option;
//                        break;
//                    case DEBUG:
//                        de.uka.ilkd.key.util.Debug.ENABLE_DEBUG = true;
//                        break;
//                    case NO_DEBUG: 
//                        de.uka.ilkd.key.util.Debug.ENABLE_DEBUG = false;
//                        break;
//                    case ASSERTION:
//                        de.uka.ilkd.key.util.Debug.ENABLE_ASSERTION = true;
//                        break;
//                    case NO_ASSERTION:
//                        de.uka.ilkd.key.util.Debug.ENABLE_ASSERTION = false;
//                        break;
//                    case NO_JMLSPECS:
//                        GeneralSettings.disableSpecs = true;
//                        break;
//                    case JUSTIFY_RULES:
//                        LinkedList<String> options = new LinkedList<String>();
//                        for(int i = index+1; i < opt.length; i++){
//                            options.add(opt[i]);
//                        }
//                        evaluateLemmataOptions(options);
//                        // is last option
//                        break loop;
//                    case PRINT_STATISTICS:
//                        if ( !( opt.length > index + 1 ) ) printUsageAndExit (true,null);
//                        statisticsFile = opt[++index];
//                        break;
//                    case TIMEOUT:
//                        long timeout = -1;
//                        try {
//                            timeout = Long.parseLong(opt[index + 1]);
//                        } catch (NumberFormatException nfe) {
//                            System.out.println("Illegal timeout (must be a number >=-1).");
//                            System.exit(-1);
//                        }
//                        if (timeout < -1) {
//                            System.out.println("Illegal timeout (must be a number >=-1).");
//                            System.exit(-1);
//                        }
//                        index++;
//                        ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setTimeout(timeout);
//                        break;
//                    case EXAMPLES:
//                        if ( !( opt.length > index + 1 ) ) printUsageAndExit (true,null);
//                        examplesDir = opt[++index];
//                        break;
//                    case HELP:
//                        printUsageAndExit(false,null);
//                    }
//                } catch (IllegalArgumentException e) {
//                    // no CommandLineOption found
//                    printUsageAndExit(true,opt[index]);
//                }
//            }
//
//            index++;
//        }
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
                    MainWindow.createInstance(getMainWindowTitle());
                    MainWindow key = MainWindow.getInstance();
                    key.setVisible(true);
                  
                }
            });
            ui = MainWindow.getInstance().getUserInterface();
            if(cl.isSet(LAST)){
            	fileNameOnStartUp = MainWindow.getInstance().getRecentFiles().getMostRecent().getAbsolutePath(); 
            	System.out.println("Loading recent File: "+fileNameOnStartUp);
            }
        }
        return ui;
    }

    private static void evaluateLemmataOptions(CommandLine options){

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

    private static void printUsageAndExit(boolean exitWithError, String offending) {
        final PrintStream ps = System.out;
        if (exitWithError) 
            ps.println("File not found or unrecognized option" +
                    (offending != null? ": "+offending: ".")+"\n");
        //ps.println("Possible parameters are (* = default): ");
//        ps.println("  <filename>      : loads a .key file");
        cl.printUsage(ps);
//        for (CommandLineOption clo: CommandLineOption.values())
//            if (clo.message != null) ps.println(clo.message);
       
        System.exit(exitWithError? -1: 0);
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
    
//    /** All possible command line options must be entered here. 
//     * @author bruns
//     */
//    private static enum CommandLineOption {
//    	TEST (null,null),
//        AUTO ('a',
//                "  auto            : start prove procedure after initialisation"),
//        AUTO_LOADONLY (null,null),
//        DEBUG ('d',
//                "  debug           : enables debug mode"),
//        NO_DEBUG ('x',
//                "  no_debug        : disables debug mode (*)"),
//        ASSERTION (null,
//                "  assertion       : enables assertions (*)"),
//        NO_ASSERTION ('n',
//                "  no_assertion    : disables assertions"),
//        NO_JMLSPECS (null,
//                "  no_jmlspecs     : disables parsing JML specifications"),
//        JUSTIFY_RULES ('r',
//                "  justify_rules    : autoprove taclets (add '?help' for instructions)"),
//        PRINT_STATISTICS ('p',
//                "  print_statistics <filename>\n" +
//                "                  : in auto mode, output nr. of rule applications and time spent"),
//        TIMEOUT ('t',
//                "  timeout <time in ms>\n"+
//                "                  : set maximal time for rule " +
//                "application in ms (-1 disables timeout)"),
//        EXAMPLES (null,null),
//        HELP ('h',
//                "  help            : display this text");
//        
//        Character shortName;
//        String message;
//        
//        /**
//         * @param shortName one-letter option, <code>null</code> if not defined
//         * @param message help text, <code>null</code> to show no help text
//         */
//        CommandLineOption(Character shortName, String message){
//            this.shortName = shortName;
//            this.message = message;
//        }
//        
//        @Override
//        public String toString() {
//            return super.toString().toLowerCase();
//        }
//    }
}
