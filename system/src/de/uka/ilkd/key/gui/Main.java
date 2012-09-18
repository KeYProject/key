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
    public static final String CHELP = "-help";
    public static final String CAUTO = "-auto";
    public static final String CAUTO_LOADONLY = "-auto_loadonly";
    public static final String CDEBUG = "-debug";
    public static final String CNO_DEBUG = "-no_debug";
    public static final String CASSERTION = "-assertion";
    public static final String CNO_ASSERTION = "-no_assertion";
    public static final String CNO_JMLSPECS = "-no_jmlspecs";
    public static final String CJUSTIFY_RULES ="-justify_rules";
    public static final String CPRINT_STATISTICS ="-print_statistics";
    public static final String CTIMEOUT ="-timeout";
    public static final String CEXAMPLES = "-examples"; 

    
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
			// TODO Auto-generated catch block
			e.printStackTrace();
			System.out.println("Exception during Commandline");
		}
        
  //    UserInterface userInterface = evaluateOptions(args);
  //    loadCommandLineFile(userInterface); 
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
    	cl.addOption(CHELP, null, "display this text");
    	cl.addOption(CAUTO, null, "start prove procedure after initialisation");
    	cl.addOption(CAUTO_LOADONLY, null, "");
    	cl.addOption(CNO_JMLSPECS, null, "disables parsing JML specifications");
    	cl.addOption(CEXAMPLES, "<examplefiles>", "loads directory with example files on startup");
    	cl.addOption(CJUSTIFY_RULES, "<options>", "autoprove taclets (add '?help' for instructions)" );
    	cl.addOption(CPRINT_STATISTICS, "<filename>",  "in auto mode, output nr. of rule applications and time spent");
    	cl.addOption(CTIMEOUT, "<timeout>", "");
    	return cl;
    }
    public static UserInterface evaluateOptions(CommandLine cl) {
//       public static UserInterface evaluateOptions(String[] opt) {
        UserInterface ui = null;
//        int index = 0;
        ProofSettings.DEFAULT_SETTINGS.setProfile(new JavaProfile());
        String uiMode = "INTERACTIVE";

        
        if(cl.isSet(CAUTO)){
        	uiMode="AUTO";
        }
        if(cl.isSet(CAUTO_LOADONLY)){
        	uiMode="AUTO_LOADONLY";
        }
        
        if(cl.isSet(CHELP)){
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
        if(cl.isSet(CNO_JMLSPECS)){
        	GeneralSettings.disableSpecs = true;
        }

        if(cl.isSet(CPRINT_STATISTICS)){
        	statisticsFile = cl.getString(CPRINT_STATISTICS, null);
        	if(statisticsFile.equals(null)){
        		printUsageAndExit(true,null);
        	}
        }
        if(cl.isSet(CTIMEOUT)){
           System.out.println("Timeout is set");
           long timeout = -1;
           try {
               timeout = (long)(cl.getInteger(CTIMEOUT, -1));
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
        if(cl.isSet(CEXAMPLES)){
        	examplesDir = cl.getString(CEXAMPLES, null);
        	if (examplesDir.equals(null)){
        		printUsageAndExit(true, null);
        	}
        }
        
     	List<String> fileArguments = cl.getArguments();
     	Iterator iter = fileArguments.iterator();
     	for (String string : fileArguments) {
			System.out.println("Hier:"+string);
		}
     	//-jr-
        if(cl.isSet(CJUSTIFY_RULES)){
            LinkedList<String> options = new LinkedList<String>();
            if (cl.getString(CJUSTIFY_RULES, null) != null){
             options.add(cl.getString(CJUSTIFY_RULES, null));
             if(!fileArguments.isEmpty()){
            	 //while()
             }
            }
            
//          for(int i = index+1; i < opt.length; i++){
//              options.add(opt[i]);
//          }
        	evaluateLemmataOptions(options);
        }
//        
        
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

    private static void printUsageAndExit(boolean exitWithError, String offending) {
        final PrintStream ps = System.out;
        if (exitWithError) 
            ps.println("File not found or unrecognized option" +
                    (offending != null? ": "+offending: ".")+"\n");
        ps.println("Possible parameters are (* = default): ");
        cl.printUsage(ps);
//        for (CommandLineOption clo: CommandLineOption.values())
//            if (clo.message != null) ps.println(clo.message);
        ps.println("  <filename>      : loads a .key file");
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
    
    /** All possible command line options must be entered here. 
     * @author bruns
     */
    private static enum CommandLineOption {
    	TEST (null,null),
        AUTO ('a',
                "  auto            : start prove procedure after initialisation"),
        AUTO_LOADONLY (null,null),
        DEBUG ('d',
                "  debug           : enables debug mode"),
        NO_DEBUG ('x',
                "  no_debug        : disables debug mode (*)"),
        ASSERTION (null,
                "  assertion       : enables assertions (*)"),
        NO_ASSERTION ('n',
                "  no_assertion    : disables assertions"),
        NO_JMLSPECS (null,
                "  no_jmlspecs     : disables parsing JML specifications"),
        JUSTIFY_RULES ('r',
                "  justify_rules    : autoprove taclets (add '?help' for instructions)"),
        PRINT_STATISTICS ('p',
                "  print_statistics <filename>\n" +
                "                  : in auto mode, output nr. of rule applications and time spent"),
        TIMEOUT ('t',
                "  timeout <time in ms>\n"+
                "                  : set maximal time for rule " +
                "application in ms (-1 disables timeout)"),
        EXAMPLES (null,null),
        HELP ('h',
                "  help            : display this text");
        
        Character shortName;
        String message;
        
        /**
         * @param shortName one-letter option, <code>null</code> if not defined
         * @param message help text, <code>null</code> to show no help text
         */
        CommandLineOption(Character shortName, String message){
            this.shortName = shortName;
            this.message = message;
        }
        
        @Override
        public String toString() {
            return super.toString().toLowerCase();
        }
    }
}
