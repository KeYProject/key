package de.uka.ilkd.key.smt;

import java.io.*;
import java.util.Calendar;

import de.uka.ilkd.key.gui.configuration.PathConfig;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.ListOfGoal;
import de.uka.ilkd.key.proof.SLListOfGoal;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.RuleApp;

public abstract class AbstractSmtProver {
        
        public static final int VALID = 0;
        public static final int INVALID = 1;
        public static final int UNKNOWN = 2;
        
        /**
         * The path for the file
         */
        private static final String fileDir = PathConfig.KEY_CONFIG_DIR + File.separator + "smt_formula";
        
        /**
         * This rule's name.
         */
        public abstract String displayName();
        
        /**
         * This rule's name as Name object.
         */
        public abstract Name name();
        
        
        /**
         * TODO overwork
         */
        public boolean isApplicable(Goal goal, PosInOccurrence pio, Constraint userConstraint) {
                boolean hasModality = false;
                
//                IteratorOfConstrainedFormula ante = goal.sequent().antecedent().iterator();
//                IteratorOfConstrainedFormula succ = goal.sequent().succedent().iterator();
                
                ModalityChecker mc = new ModalityChecker();
                
                for (final ConstrainedFormula currentForm : goal.sequent()) {
                        currentForm.formula().execPreOrder(mc);   
                        if (mc.hasModality()) {
                                hasModality = true;
                        }
                        mc.reset();
                }
                return true;
        }
        
        /**
         * Get the abstract translator, that should be used to
         * @return the translator, that should be used.
         */
        protected abstract AbstractSmtTranslator getTranslator(Goal goal, Services services, RuleApp ruleApp);
        
        /**
         * Get the command for executing an external proofer.
         * @param filename the location, where the file is stored.
         * @param formula the formula, that was created by the translator
         * @return Array of Strings, that can be used for executing an external decider.
         */
        protected abstract String[] getExecutionCommand(String filename, StringBuffer formula);
        
        private static String toStringLeadingZeros ( int n, int width ) {
                String rv = "" + n;
                while ( rv.length() < width ) {
                    rv = "0" + rv;
                }
                return rv;
            }
        
        /**
         * Constructs a date for use in log filenames.
         */
        private static String getCurrentDateString () {
            Calendar c = Calendar.getInstance();
            StringBuffer sb = new StringBuffer();
            String dateSeparator = "-";
            String dateTimeSeparator = "_";
            sb.append(toStringLeadingZeros(c.get(Calendar.YEAR), 4))
              .append( dateSeparator )
              .append(toStringLeadingZeros(c.get(Calendar.MONTH) + 1, 2))
              .append( dateSeparator )
              .append(toStringLeadingZeros(c.get(Calendar.DATE), 2))
              .append( dateTimeSeparator )
              .append(toStringLeadingZeros(c.get(Calendar.HOUR_OF_DAY), 2) +"h" )
              .append(toStringLeadingZeros(c.get(Calendar.MINUTE), 2) + "m" )
              .append(toStringLeadingZeros(c.get(Calendar.SECOND), 2) + "s" )
              .append('.')
              .append(toStringLeadingZeros(c.get(Calendar.MILLISECOND), 2));
            return sb.toString();
        }
        
        /**
         * store the text to a file.
         * @param text the text to be stored.
         * @return the path, where the file was stored to.
         */
        private final String storeToFile(StringBuffer text) throws IOException {
                String loc = fileDir + getCurrentDateString();
                new File( fileDir ).mkdirs();
                BufferedWriter out = new BufferedWriter(new FileWriter(loc));
                out.write(text.toString());
                out.close();
                
                return loc;
        }
        
        /**
         * 
         * @param answer the String answered by the external programm
         * @return VALID, if the formula was proven valid, 
         *      INVALID, if the formula was proven invalid,
         *      UNKNOWN, if the formula could not be proved
         */
        protected abstract int answerType(String answer);
        
        /** Read the input until end of file and return contents in a
         * single string containing all line breaks. */
        private static String read ( InputStream in ) throws IOException {
            BufferedReader reader = new BufferedReader
                (new InputStreamReader(in));
            StringBuffer sb = new StringBuffer();
            int x = reader.read();
            while(x > -1) {
                    sb.append((char)x);
                    x = reader.read();
            }
            return sb.toString();
        }
        
        /**
         * called by the System. Here the actual decision is made.
         */
        public final int isValid(Goal goal, Services services, RuleApp ruleApp) {
                int toReturn = UNKNOWN;
                //toReturn.append(goal);
                
                try {
                        //get the translation
                        AbstractSmtTranslator trans = this.getTranslator(goal, services, ruleApp);
                        String loc;
//                        SMTTranslator trans = new SMTTranslator(goal.sequent(), new ConstraintSet(goal, null), SetAsListOfMetavariable.EMPTY_SET, services);
                        
                        try {
                                StringBuffer s = trans.translate(goal.sequent(), services);
                                //store the translation to a file                                
                                loc = this.storeToFile(s);
                                //get the commands for execution
                                String[] execCommand = this.getExecutionCommand(loc, s);
                                
                                try {
                                
                                        Process p = Runtime.getRuntime().exec(execCommand);
                                        try {
                                                p.waitFor();
                                        } catch (InterruptedException f) {
                                                //TODO react
                                                System.out.println("process was interrupted");
                                        }

                                
                                        InputStream in = p.getInputStream();
                                        String result = read(in);
                                        in.close();                                
                                        int validity = this.answerType(result);
                                        if (validity == VALID) {
                                                //toReturn = SLListOfGoal.EMPTY_LIST;
                                                toReturn = VALID;
                                        } else if (validity == INVALID) {
                                                //toReturn = SLListOfGoal.EMPTY_LIST;
                                                //toReturn.append(goal);
                                                toReturn = INVALID;
                                        } else {
                                                //toReturn = SLListOfGoal.EMPTY_LIST;
                                                //toReturn.append(goal);
                                                toReturn = UNKNOWN;
                                        }
                                } catch (IOException e) {
                                        //TODO react
                                        System.out.println("Program could not be executed");
                                } finally {
                                        //remove the created file
                                        File f = new File(loc);
                                        f.delete();
                                }
                        } catch (IOException e) {
                                //TODO react on this
                                //file could not be written
                                System.out.println("File could not be written");
                        }
                } catch (IllegalFormulaException e) {
                        //toReturn = SLListOfGoal.EMPTY_LIST;
                        //toReturn.append(goal);
                        toReturn = UNKNOWN;
                        //TODO log message
                        System.out.println("!!!    Illegal Formula Exception thrown");
                }
                return toReturn;
        }

}
