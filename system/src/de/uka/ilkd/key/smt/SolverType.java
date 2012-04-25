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

        /**
         * Checks whether the solver is installed. If <code>recheck</code> is set to true
         * the method should check for the path variable of the system and for the absolute path,
         * otherwise it can return the result of the previous call.
         */
        public boolean isInstalled(boolean recheck);

        /**
         * Some specific information about the solver which can be presented. <code>null</code> means no information. 
         */
        public String getInfo();

        /**
         * The currently used parameters for the solver.
         */
        public String getSolverParameters();
        public void setSolverParameters(String s);
        /** The default parameters which should be used for starting a solver */
        public String getDefaultSolverParameters();
        
        
        /** the command for starting the solver. For example "z3" if it is registered in the PATH variable,
         * otherwise "ABSOLUTE_PATH/z3"*/        
        public String getSolverCommand();
        public void setSolverCommand(String s);
        public String getDefaultSolverCommand();
      
       
        /**
         * The translator to be used. So far each solver supports only one format. 
         */
        public SMTTranslator getTranslator(Services services);
        /**
         * The delimiters of the messages that are sent from the solver to KeY. For example it could be "\n"
         */
        public String[]  getDelimiters();
        
        public boolean supportsIfThenElse();
        
        /**
         * Directly before the problem description is sent to the solver one can modify the problem string by using
         * this method.
         */
        public String modifyProblem(String problem);

        /**
         * Class for the Z3 solver. It makes use of the SMT2-format.
         */
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
                
                public String[] getDelimiters() {
                	return new String [] {"\n","\r"};
                };

                public boolean supportsIfThenElse() {
                        return true;
                };
                @Override
                public SMTTranslator getTranslator(Services services) {
                        return new SmtLib2Translator(services,
                                        new Configuration(false,false));
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
					if(type == Pipe.ERROR_MESSAGE || message.startsWith("(error")){
						 sc.addMessage(message);
						 if(message.indexOf("WARNING:")>-1){
							return;
						 }
						 throw new RuntimeException("Error while executing Z3:\n" +message);
					 }
			
			
				switch (sc.getState()) {
				case WAIT_FOR_RESULT:
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
						 sc.setFinalResult(SMTSolverResult.createUnknownResult(getName()));
					 }
					break;
					
				case WAIT_FOR_DETAILS:
					if(message.equals("success")){
						pipe.close();	
					}else{
						sc.addMessage(message);
					}						
					break;						
				}
			}

        };
        
        
        /**
         * Class for the CVC3 solver. It makes use of the SMT1-format.
         */
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
                    return "+lang smt +model +int";
                }
                
                public String[] getDelimiters() {
                	return new String [] {"CVC>","C>"};
                };

                @Override
                public SMTTranslator getTranslator(Services services) {
                        return new SmtLibTranslator(services,
                                        new Configuration(false,true));
                }
                
                public boolean supportsIfThenElse() {
                        return true;
                };

                @Override
                public String getInfo() {
                        return null;
                }

               
                
                final static int WAIT_FOR_RESULT=0;
                final static int FINISH = 1;
				@Override
				public void messageIncoming(Pipe<SolverCommunication> pipe, String message, int type) {
					 SolverCommunication sc = pipe.getSession();
					 sc.addMessage(message);
					 if(type == Pipe.ERROR_MESSAGE){
						 throw new RuntimeException("Error while executing CVC:\n" +message);
					 }
					 
					 if(sc.getState() == WAIT_FOR_RESULT ){
						 if(message.indexOf(" sat") > -1){
							 sc.setFinalResult(SMTSolverResult.createInvalidResult(getName()));
						 }
						 if(message.indexOf(" unsat") > -1){
							 sc.setFinalResult(SMTSolverResult.createValidResult(getName()));
						 }
						 sc.setState(FINISH);
					     pipe.close();
					     
					 }
					
				}

        };
        
        
        /**
         * Class for the Yices solver. It makes use of the SMT1-format.
         */
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
                                        new Configuration(true,true));
                }

                         
                @Override
                public String getDefaultSolverCommand() {
                          return "yices";
                }
                
                public String[] getDelimiters() {
                	return new String [] {"\n","\r"};
                };
                
                @Override
                public String getDefaultSolverParameters() {
                         return "-i -e -smt";
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
				public void messageIncoming(Pipe<SolverCommunication> pipe, String message, int type) {
					SolverCommunication sc = pipe.getSession();
					message = message.replaceAll("\n","");
					sc.addMessage(message);		
					
							
					if(message.equals("unsat")){
						 sc.setFinalResult(SMTSolverResult.createValidResult(getName()));						
						 pipe.close();
					}
					if(message.equals("sat")){
						 sc.setFinalResult(SMTSolverResult.createInvalidResult(getName()));						 
						 pipe.close();
					}
					
				}
				
				public String modifyProblem(String problem) {
					return problem += "\n\n check\n";
				};

        };
        
        /**
         * Class for the CVC3 solver. It makes use of its own format.
         */
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
                
                public String[] getDelimiters() {
                	return new String [] {">"};
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
				public void messageIncoming(Pipe<SolverCommunication> pipe,String message, int type) {
					SolverCommunication sc = pipe.getSession();
					sc.addMessage(message);		
					
							
					if(message.indexOf("Valid.")>-1){
						 sc.setFinalResult(SMTSolverResult.createValidResult(getName()));						
						 pipe.close();
					}
					
					if(message.indexOf("Invalid.")>-1){
						 sc.setFinalResult(SMTSolverResult.createInvalidResult(getName()));						 
						 pipe.close();
					}
					
					if(message.indexOf("Bad input:")>-1){
						pipe.close();
					}
					
							
					
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
        
        @Override
        public String modifyProblem(String problem) {
        return problem;
        }

}
