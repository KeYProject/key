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

package de.uka.ilkd.key.gui.lemmatagenerator;

import java.io.File;
import java.io.PrintStream;
import java.util.Collection;
import java.util.LinkedList;

import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.util.CommandLine;
import de.uka.ilkd.key.util.CommandLineException;

public class LemmataAutoModeOptions {
        public static final int DEFAULT_TIMEOUT = -1;
        public static final int DEFAULT_MAXRULES = 10000;
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
        public LemmataAutoModeOptions(CommandLine cl, String internalVersion) {
                super();
                try{
                	if(cl.isSet(Main.JUSTIFY_RULES)){
                		this.pathOfRuleFile = cl.getString(Main.JUSTIFY_RULES, null);
                	
                	}
                	if(cl.isSet(Main.JTIMEOUT)){
                		this.timeout = cl.getLong(Main.JTIMEOUT, DEFAULT_TIMEOUT);
                		System.out.println("We are in cons 1 and timeout is "+timeout);
                	}
                	if(cl.isSet(Main.JMAX_RULES)){
                		this.maxRules =  cl.getInteger(Main.JMAX_RULES, DEFAULT_MAXRULES);
                	}
                	if(cl.isSet(Main.JPATH_OF_RESULT) && cl.isSet(Main.JUSTIFY_RULES)){
                		this.pathOfResult = generatePath(cl.getString(Main.JPATH_OF_RESULT, null), pathOfRuleFile);
                	}
                	}catch(CommandLineException cle){
                		System.out.println("There was a problem reading the command line options. An argument is missing either for option "+Main.JTIMEOUT+ " or "+Main.JMAX_RULES+".");
                		
                	
                	}
                this.internalVersion = internalVersion;
                checkForValidity();// throws an exception if a parameter is not
                                   // valid.
        }

        public LemmataAutoModeOptions(CommandLine cl,
                        String internalVersion, String homePath) {
                this.internalVersion = internalVersion;
                
                if(cl.isSet(Main.JUSTIFY_RULES)){
                	this.pathOfRuleFile = cl.getString(Main.JUSTIFY_RULES, null); 
                }
                System.out.println("We are in cons 2");
                read(cl);
                pathOfResult = generatePath(pathOfResult, pathOfRuleFile);
                this.homePath = homePath;
                checkForValidity();
        }
        private void read(CommandLine cl) {
                if (cl.isSet(Main.JMAX_RULES)) {
                		try {
							cl.getInteger(Main.JMAX_RULES, DEFAULT_MAXRULES);
						} catch (CommandLineException e) {
							System.out.println("Commandline argument for option "+Main.JMAX_RULES+"is missing.");
						}
                }
                if (cl.isSet(Main.JPATH_OF_RESULT)) {
                	pathOfResult = cl.getString(Main.JPATH_OF_RESULT, null);
                }
                if (cl.isSet(Main.JUSTIFY_RULES)) {
                	pathOfRuleFile = cl.getString(Main.JUSTIFY_RULES, null);
                }
                if (cl.isSet(Main.JTIMEOUT)) {
                	try {
						timeout = cl.getLong(Main.JTIMEOUT, DEFAULT_TIMEOUT);
						System.out.println("Timeout2 is :"+timeout);
					} catch (CommandLineException e) {
						System.out.println("Commandline argument for "+Main.JTIMEOUT+" is missing.");
					}
                }
                if (cl.isSet(Main.JPRINT)) {
                        if (cl.getString(Main.JPRINT, "terminal").equals("terminal")) {
                                printStream = System.out;
                        }
                        if (cl.getString(Main.JPRINT, "terminal").equals("disable")) {
                                printStream = null;
                        }
                }
                if (cl.isSet(Main.JSAVE_RESULTS_TO_FILE)) {
                		saveResultsToFile = readBoolean(cl.getString(Main.JSAVE_RESULTS_TO_FILE, "false"), saveResultsToFile);
                }
                if (cl.isSet(Main.JFILE_FOR_AXIOMS)) {
                        filesForAxioms.add(cl.getString(Main.JFILE_FOR_AXIOMS, null));
                }
                if (cl.isSet(Main.JFILE_FOR_DEFINITION)) {
                        pathOfDefinitionFile = cl.getString(Main.JFILE_FOR_DEFINITION, null);
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



}