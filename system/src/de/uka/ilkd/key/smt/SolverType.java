// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.smt;

import java.io.File;


import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.smt.AbstractSMTTranslator.Configuration;

public interface SolverType extends PipeListener<SolverCommunication> {

        public SMTSolver createSolver(SMTProblem problem,
                        SolverListener listener, Services services);

        public String getName();

        public boolean isInstalled(boolean recheck);

        public void useTaclets(boolean b);

        public SMTSolverResult interpretAnswer(String text, String error,
                        int val);

        public String getInfo();
        
        public String getSolverCommand();




        public String getSolverParameters();
        

        public void setSolverParameters(String s);
        
        public void setSolverCommand(String s);

        public String getDefaultSolverParameters();
        
        public String getDefaultSolverCommand();

        public SMTTranslator getTranslator(Services services);
        
        public boolean supportsIfThenElse();

        static public final SolverType Z3_SOLVER = new AbstractSolverType() {

                      
                public String getDefaultSolverCommand() {
                    return "z3";                    
                };
                
                public String getDefaultSolverParameters() {
                    return "-in -smt2";
                };

                @Override
                public SMTSolver createSolver(SMTProblem problem,
                                SolverListener listener, Services services) {
                        return new SMTSolverImplementation(problem, listener,
                                        services, this);
                }

                @Override
                public String getName() {
                        return "Z3";
                }

                public boolean supportsIfThenElse() {
                        return true;
                };
                @Override
                public SMTTranslator getTranslator(Services services) {
                        return new SmtLib2Translator(services,
                                        new Configuration(false));
                }

                public SMTSolverResult interpretAnswer(String text,
                                String error, int val) {
                        if (val == 0) {
                                // no error occured
                                if (text.contains("unsat")) {
                                        return SMTSolverResult
                                                        .createValidResult(
                                                                        getName());
                                } else if (text.contains("sat")) {
                                        return SMTSolverResult
                                                        .createInvalidResult(
                                                                        
                                                                        getName());
                                } else {
                                        return SMTSolverResult
                                                        .createUnknownResult(
                                                                        
                                                                        getName());
                                }
                        } else if ((val == 112 && text.contains("unknown"))
                                        || val == 139) {
                                // the result was unknown
                                return SMTSolverResult.createUnknownResult(
                                                 getName());
                        } else {
                                // something went wrong
                                throw new IllegalResultException("Code " + val
                                                + ": " + error);
                        }
                }

                @Override
                public String getInfo() {

                        return "Z3 does not use quantifier elimination by default. This means for example that"
                                        + " the following problem cannot be solved automatically by default:\n\n"
                                        + "\\functions{\n"
                                        + "\tint n;\n"
                                        + "}\n\n"
                                        + "\\problem{\n"
                                        + "\t((\\forall int x;(x<=0 | x >= n+1)) & n >= 1)->false\n"
                                        + "}"
                                        + "\n\n"
                                        + "You can activate quantifier elimination by appending QUANT_FM=true to"
                                        + " the execution command.";
                }

                private static final int WAIT_FOR_RESULT = 0;
                private static final int WAIT_FOR_DETAILS =1;
                
                
				@Override
				public void messageIncoming(Pipe<SolverCommunication> pipe, String message, int type) {
					SolverCommunication sc = pipe.getSession();
				switch (sc.getState()) {
					case WAIT_FOR_RESULT:
						 if(type == Pipe.ERROR_MESSAGE || message.startsWith("(error")){
							 throw new RuntimeException("Error while executing Z3:\n" +message);
						 }
						 if(message.equals("unsat")){
							 sc.setFinalResult(SMTSolverResult.createValidResult(getName()));
							 pipe.sendMessage("(get-proof)\n");
							 pipe.sendMessage("(exit)\n");
							 sc.setState(WAIT_FOR_DETAILS);
						 }
						 if(message.equals("sat")){
							 sc.setFinalResult(SMTSolverResult.createInvalidResult(getName()));
							 pipe.sendMessage("(get-model)");
							 pipe.sendMessage("(exit)\n");
							 sc.setState(WAIT_FOR_DETAILS);
						 }
						 if(message.equals("unkown")){
							 sc.setFinalResult(SMTSolverResult.createInvalidResult(getName()));
						 }
						break;
						
					case WAIT_FOR_DETAILS:
						if(message.equals("success")){
							pipe.stop();	
						}else{
							sc.addMessage(message);
						}						
						break;						
					}
					
				}

        };
        static public final SolverType CVC3_SOLVER = new AbstractSolverType() {

                @Override
                public String getName() {
                        return "CVC3";
                }

                @Override
                public SMTSolver createSolver(SMTProblem problem,
                                SolverListener listener, Services services) {
                        return new SMTSolverImplementation(problem, listener,
                                        services, this);
                }

                public String getDefaultSolverCommand() {
                    return "cvc3";
                };
                
                @Override
                public String getDefaultSolverParameters() {
                    // TODO Auto-generated method stub
                    return " -lang smt +model %f";
                }

                @Override
                public SMTTranslator getTranslator(Services services) {
                        return new SmtLibTranslator(services,
                                        new Configuration(false));
                }
                
                public boolean supportsIfThenElse() {
                        return true;
                };

                @Override
                public String getInfo() {
                        return null;
                }

                @Override
                public SMTSolverResult interpretAnswer(String text,
                                String error, int val) {
                        if (val == 0) {
                                // normal termination, no error
                                if (text.startsWith("unsat\n")) {
                                        return SMTSolverResult
                                                        .createValidResult(
                                                                        
                                                                        getName());
                                } else if (text.startsWith("sat\n")) {
                                        return SMTSolverResult
                                                        .createInvalidResult(
                                                                        
                                                                        getName());
                                } else {
                                        return SMTSolverResult
                                                        .createUnknownResult(
                                                                        
                                                                        getName());
                                }
                        } else {
                                // error termination
                                throw new IllegalResultException(error);
                        }
                }

				@Override
				public void messageIncoming(Pipe<SolverCommunication> pipe, String message, int type) {
					// TODO Auto-generated method stub
					
				}

        };
        static public final SolverType YICES_SOLVER = new AbstractSolverType() {

                @Override
                public String getName() {
                        return "Yices";
                }

                @Override
                public SMTSolver createSolver(SMTProblem problem,
                                SolverListener listener, Services services) {
                        return new SMTSolverImplementation(problem, listener,
                                        services, this);
                }

                @Override
                public SMTTranslator getTranslator(Services services) {
                        return new SmtLibTranslator(services,
                                        new Configuration(true));
                }

                         
                @Override
                public String getDefaultSolverCommand() {
                          return "yices";
                }
                
                @Override
                public String getDefaultSolverParameters() {
                         return "-tc -e -smt %f";
                }

                @Override
                public String getInfo() {
                        return "Use the newest release of version 1.x instead of version 2. Yices 2 does not support the "
                                        + "required logic AUFLIA.";
                }
                
                public boolean supportsIfThenElse() {
                        return true;
                };

                @Override
                public SMTSolverResult interpretAnswer(String text,
                                String error, int val) {
                        if (val == 0) {
                                if (text.startsWith("unsat\n")) {
                                        return SMTSolverResult
                                                        .createValidResult(
                                                                    
                                                                        getName());
                                } else if (text.startsWith("sat\n")) {
                                        return SMTSolverResult
                                                        .createInvalidResult(
                                                                        
                                                                        getName());
                                } else {
                                        return SMTSolverResult
                                                        .createUnknownResult(
                                                                       
                                                                        getName());
                                }

                        } else {
                                throw new IllegalResultException(error);
                        }

                }

				@Override
				public void messageIncoming(Pipe<SolverCommunication> pipe, String message, int type) {
					// TODO Auto-generated method stub
					
				}

        };
        static public final SolverType SIMPLIFY_SOLVER = new AbstractSolverType() {


                @Override
                public String getName() {
                        return "Simplify";
                }

                @Override
                public SMTSolver createSolver(SMTProblem problem,
                                SolverListener listener, Services services) {
                        return new SMTSolverImplementation(problem, listener,
                                        services, this);
                }

                @Override
                public SMTTranslator getTranslator(Services services) {
                        return new SimplifyTranslator(services,
                                        new Configuration(false,true));
                }
                
                public String getDefaultSolverCommand() {
                    return "simplify";
                };
                
                public String getDefaultSolverParameters() {
                    return "-print";
                };

         
                @Override
                public String getInfo() {
                        return "Simplify only supports integers within the interval [-2147483646,2147483646]=[-2^31+2,2^31-2].";
                }
                
                public boolean supportsIfThenElse() {
                        return false;
                };

                @Override
                public SMTSolverResult interpretAnswer(String text,
                                String error, int val) {
                        if (val == 0) {
                                // no error occured
                                if (meansValid(text)) {
                                        return SMTSolverResult
                                                        .createValidResult(
                                                                      
                                                                        getName());
                                } else if (meansInvalid(text)) {
                                        return SMTSolverResult
                                                        .createInvalidResult(
                                                                       
                                                                        getName());
                                } else if (meansBadInput(text)) {
                                        throw new IllegalResultException(text);

                                } else {
                                        return SMTSolverResult
                                                        .createUnknownResult(
                                                                       
                                                                        getName());
                                }
                        } else {
                                // error occured
                                throw new IllegalResultException(error);
                        }

                }

                private boolean meansBadInput(String text) {
                        return text.indexOf("Bad input") >= 0;
                }

            

        

                private boolean meansValid(String text) {
                        boolean toReturn = false;
                        String wanted = "Valid.";
                        int pos = text.indexOf(wanted);
                        if (pos != -1) {
                                // Valid. is found. check, if it is on the end
                                // of the String and
                                // if only \n are following
                                toReturn = true;
                                pos = pos + wanted.length();
                                for (int i = pos + 1; i < text.length(); i++) {
                                        if (text.charAt(i) != '\n'
                                                        && text.charAt(i) != ' ') {
                                                toReturn = false;
                                        }
                                }
                        }
                        return toReturn;
                }

                private boolean meansInvalid(String text) {
                        boolean toReturn = false;
                        String wanted = "Invalid.";
                        int pos = text.indexOf(wanted);
                        if (pos != -1) {
                                // Valid. is found. check, if it is on the end
                                // of the String and
                                // if only \n are following
                                toReturn = true;
                                pos = pos + wanted.length();
                                for (int i = pos + 1; i < text.length(); i++) {
                                        if (text.charAt(i) != '\n'
                                                        && text.charAt(i) != ' ') {
                                                toReturn = false;
                                        }
                                }
                        }
                        return toReturn;
                }

				@Override
				public void messageIncoming(Pipe<SolverCommunication> pipe,String message, int type) {
					SolverCommunication sc = pipe.getSession();
				    if(message.indexOf("Bad input")>-1){
						 sc.setFinalResult(SMTSolverResult.createInvalidResult(getName()));
					}
					
					if(message.indexOf("Valid.")>-1){
						 sc.setFinalResult(SMTSolverResult.createValidResult(getName()));						
						 pipe.stop();
					}
					
					if(message.indexOf("Invalid.")>-1){
						 sc.setFinalResult(SMTSolverResult.createInvalidResult(getName()));
						 
						 pipe.stop();
					}				
					sc.addMessage(message);		
					
				}
        };

}

abstract class AbstractSolverType implements SolverType {
        private boolean installWasChecked = false;
        private boolean isInstalled = false;
        private String solverParameters = getDefaultSolverParameters();
        private String solverCommand    = getDefaultSolverCommand();


        public static boolean isInstalled(String cmd) {

         
                if (checkEnvVariable(cmd)) {
                        return true;
                } else {

                        File file = new File(cmd);

                        return file.exists();

                }
        }

        @Override
        public void useTaclets(boolean b) {

        }

        /**
         * check, if this solver is installed and can be used.
         * 
         * @param recheck
         *                if false, the solver is not checked again, if a cached
         *                value for this exists.
         * @return true, if it is installed.
         */
        public boolean isInstalled(boolean recheck) {
                if (recheck || !installWasChecked) {

                        String cmd = getSolverCommand();
                    
                        isInstalled = isInstalled(cmd);
                        if (isInstalled) {
                                installWasChecked = true;
                        }

                }
                return isInstalled;
        }

        private static boolean checkEnvVariable(String cmd) {
                String filesep = System.getProperty("file.separator");
                String path = System.getenv("PATH");
  
                String[] res = path.split(System.getProperty("path.separator"));
                for (String s : res) {
                        File file = new File(s + filesep + cmd);
                        if (file.exists()) {
                                return true;
                        }
                }

                return false;

        }
  

        public String getSolverParameters() {
                if(solverParameters == null){
                    return getDefaultSolverParameters();
                }
                return solverParameters;
        }

        public void setSolverParameters(String s) {

                solverParameters= s;
        }
        
        @Override
        public void setSolverCommand(String s) {
            solverCommand = s;
        }
        
        @Override
        public final String getSolverCommand() {
            if(solverCommand == null || solverCommand.isEmpty()){
                return getDefaultSolverCommand();
            }
            return solverCommand;
        }
        
        
        @Override
        public void exceptionOccurred(Pipe<SolverCommunication> pipe,
        	Throwable exception) {
        	pipe.getSession().addException(exception);
        
        }
        

        public String toString() {
                return getName();
        }

}
