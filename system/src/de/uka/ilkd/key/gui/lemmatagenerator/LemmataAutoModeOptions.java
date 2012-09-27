package de.uka.ilkd.key.gui.lemmatagenerator;

import java.io.File;
import java.io.PrintStream;
import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedList;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.util.CommandLine;
import de.uka.ilkd.key.util.CommandLineException;

public class LemmataAutoModeOptions {
        private static final int DEFAULT_TIMEOUT = -1;
        private static final int DEFAULT_MAXRULES = 10000;
        private static final String PRINT_TERMINAL = "terminal";
        private static final String PRINT_DISABLE = "disable";
        private static final String KEY_PREFIX = "?";
        private static final String MAX_RULES = KEY_PREFIX + "maxRules";
        private static final String PATH_OF_RULE_FILE = KEY_PREFIX + "pathOfRuleFile";
        private static final String PATH_OF_RESULT = KEY_PREFIX + "pathOfResult";
        private static final String TIMEOUT = KEY_PREFIX + "timeout";
        private static final String PRINT = KEY_PREFIX + "print";
        private static final String SAVE_RESULTS_TO_FILE = KEY_PREFIX + "saveProofToFile";
        private static final String FILE_FOR_AXIOMS = KEY_PREFIX + "axioms";
        private static final String FILE_FOR_DEFINITION = KEY_PREFIX +"signature";
        private static final String JUSTIFY_RULES ="-justify_rules";
        private static final String PROOF_POSTFIX = ".key.proof";

        /**
         * The path of the file containing the rules that should be proven.
         * */
        private String pathOfRuleFile;
        
        /**
         * CommandLine object, where all options are parsed already
         */
        
        private CommandLine cl;
        
        private Collection<String> filesForAxioms = new LinkedList<String>();

        /**
         * The names of the rules that should be proven. If this container is
         * empty this means that every rule contained in
         * <code>pathRuleFile</code> must be proven.
         */
        private final LinkedList<String> rules = new LinkedList<String>();
        /**
         * The time out for each proof. If <code>timeout<0</code> no time out is
         * used.
         */
        private long timeout = DEFAULT_TIMEOUT;

        /**
         * The maximum number of rules that are used within a proof.
         */
        private int maxRules = DEFAULT_MAXRULES;

        private String pathOfResult = "";
        
        private String pathOfDefinitionFile ="";

        private PrintStream printStream = System.out;

        /**
         * Contains the internal version of KeY. It is needed for saving proofs.
         */
        private final String internalVersion;

        /**
         * If this option is activated, the resulting proofs are stored in files
         * within the folder <code>pathOfResult</code>.
         */
        private boolean saveResultsToFile = false;

        private String homePath;
//        public LemmataAutoModeOptions(String pathRuleFile, int timeout,
//        		-                        int maxRules, String pathResult, String internalVersion) {
        public LemmataAutoModeOptions(CommandLine cl, String internalVersion) {
                super();
                try{
                	if(cl.isSet(PATH_OF_RULE_FILE)){
                		this.pathOfRuleFile = cl.getString(PATH_OF_RULE_FILE, null);
                	
                	}
                	if(cl.isSet(TIMEOUT)){
                		this.timeout = cl.getLong(TIMEOUT, DEFAULT_TIMEOUT);
                	}
                	if(cl.isSet(MAX_RULES)){
                		this.maxRules =  cl.getInteger(MAX_RULES, DEFAULT_MAXRULES);
                	}
                	if(cl.isSet(PATH_OF_RESULT) && cl.isSet(PATH_OF_RULE_FILE)){
                		this.pathOfResult = generatePath(cl.getString(PATH_OF_RESULT, null), pathOfRuleFile);
                	}
                	}catch(CommandLineException cle){
                		System.out.println("There was a problem reading the command line options");
                	
                	}
                this.internalVersion = internalVersion;
                checkForValidity();// throws an exception if a parameter is not
                                   // valid.
        }

        public LemmataAutoModeOptions(CommandLine cl,
                        String internalVersion, String homePath) {
                this.internalVersion = internalVersion;
                
                if(cl.isSet(JUSTIFY_RULES)){
                	//if cascade
                }
//                if (options.isEmpty()) {
//                    printUsage();
//                    throwError("No parameters were specified");
//                }
//                if (!options.getFirst().equals(PATH_OF_RULE_FILE)) {
//                        options.addFirst(PATH_OF_RULE_FILE);
//                }
//                analyzeParameters(options);
//                pathOfResult = generatePath(pathOfResult, pathOfRuleFile);
//                this.homePath = homePath;
//                checkForValidity();
        }

        private void analyzeParameters(LinkedList<String> options) {
                Iterator<String> it = options.iterator();
                while (it.hasNext()) {
                        String option = it.next();
                        if (option.startsWith(KEY_PREFIX)) {
                                if (it.hasNext()) {
                                        read(option, it.next());
                                } else {
                                        throwError("There is no parameter specified for option "
                                                        + option);
                                }
                        } else {
                                rules.add(option);
                        }
                }
        }

        private void read(String key, String value) {
                if (key.equals(MAX_RULES)) {
                        maxRules = Integer.parseInt(value);
                }
                if (key.equals(PATH_OF_RESULT)) {
                        pathOfResult = value;
                }
                if (key.equals(PATH_OF_RULE_FILE)) {
                        pathOfRuleFile = value;
                }
                if (key.equals(TIMEOUT)) {
                        timeout = Long.parseLong(value);
                }
                if (key.equals(PRINT)) {
                        if (value.equals(PRINT_TERMINAL)) {
                                printStream = System.out;
                        }
                        if (value.equals(PRINT_DISABLE)) {
                                printStream = null;
                        }
                }
                if (key.equals(SAVE_RESULTS_TO_FILE)) {
                        saveResultsToFile = readBoolean(value,
                                        saveResultsToFile);
                }
                if (key.equals(FILE_FOR_AXIOMS)) {
                        filesForAxioms.add(value);
                }
                if (key.equals(FILE_FOR_DEFINITION)) {
                        pathOfDefinitionFile = value;
                }
        }

        private boolean readBoolean(String value, boolean def) {
                if (value.equals("true")) {
                        return true;
                } else if (value.equals("false")) {
                        return false;
                }
                return def;
        }

        public String getPathOfDefinitionFile() {
                return pathOfDefinitionFile;
        }
        public String getHomePath() {
                return homePath;
        }

        public boolean isSavingResultsToFile() {
                return saveResultsToFile;
        }

        public String getPathOfRuleFile() {
                return pathOfRuleFile;
        }

        public int getMaxNumberOfRules() {
                return maxRules;
        }

        public long getTimeout() {
                return timeout;
        }

        public PrintStream getPrintStream() {
                return printStream;
        }

        public String getInternalVersion() {
                return internalVersion;
        }

        public String createProofPath(Proof p) {
                return pathOfResult + File.separator + p.name() + PROOF_POSTFIX;
        }

        private void checkForValidity() {
                File test = new File(pathOfRuleFile);
                if (!test.isFile()) {
                        throwError("Error while setting the file containing the rules:\n"
                                        + pathOfRuleFile
                                        + " is not a valid file in your system.");
                }
                test = new File(pathOfResult);
                if (!test.isDirectory()) {
                        throwError("Error while setting the folder of the results:\n"
                                        + pathOfResult + " is not a folder.");
                }
                
        }

        private void throwError(String error) {
                throw new IllegalArgumentException(error);
        }

        private String generatePath(String path, String reference) {
                if (path.equals("")) {
                        File temp = new File(reference);
                        int index = temp.getAbsolutePath().lastIndexOf(File.separator);
                        path = temp.getAbsolutePath().substring(0, index + 1);
                }
                return path;
        }

        public String toString() {
                String s = "";
                s += "path of rule file: " + pathOfRuleFile + "\n";
                s += "path of result: " + pathOfResult + "\n";
                s += "maximum number of rules: " + maxRules + "\n";
                s += "timeout: " + timeout + "\n";
                s += "save proof to file:" + saveResultsToFile + "\n";
                return s;
        }

        public Collection<String> getFilesForAxioms() {
                return filesForAxioms;
        }

        public static void printUsage() {
//            System.out.println("The 'justifyrules' command has a number options you can set.");
//            System.out.println("Provide the option name and the value as separate arguments.");
//            System.out.println(" ?print           where to send output (use 'terminal' or 'disable')");
//            System.out.println(" ?maxRules        the maximum number of rule application to perform ");
//            System.out.println("                    (default: " + DEFAULT_MAXRULES + ")");
//            System.out.println(" ?pathOfRuleFile  the file to load the rules from");
//            System.out.println(" ?pathOfResult    the folder to store proofs to");
//            System.out.println(" ?timeout         the timeout in ms (default: " + DEFAULT_TIMEOUT +")");
//            System.out.println(" ?saveProofToFile flag to save or drop proofs (use 'true'/'false'),"); 
//            System.out.println("                    (then stored to path given by ?pathOfResult)");
//            System.out.println(" ?signature       file to read definitions from");
//            System.out.println();
//            System.out.println("If first argument does not start with '?', an implicit leading");
//            System.out.println("?pathOfRuleFile is assumed. For further information see the help");
//            System.out.println("for the dialog reached under \"File > Prove > Userdefined Taclets\"");
        }

}
