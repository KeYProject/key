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

package de.uka.ilkd.key.smt;

import java.io.File;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.smt.AbstractSMTTranslator.Configuration;


/**
 * This interface is used for modeling different solvers. It provides methods that encode information
 * about the concrete solver:
 * - name 
 * - command for starting the solver
 * - parameters
 * - supported versions
 *
 */
public interface SolverType  {

	/**
	 * Creates an instance of SMTSolver representing a concrete instance of that solver.
	 * 		 */
	public SMTSolver createSolver(SMTProblem problem,
			SolverListener listener, Services services);

	/**
	 * Returns the name of the solver.
	 *   */
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
	public SMTTranslator createTranslator(Services services);
	/**
	 * The delimiters of the messages that are sent from the solver to KeY. For example it could be "\n"
	 */
	public String[]  getDelimiters();

	/**
	 * Returns true if and only if the solver supports if-then-else terms.
	 *          */
	public boolean supportsIfThenElse();

	/**
	 * Directly before the problem description is sent to the solver one can modify the problem string by using
	 * this method.
	 */
	public String modifyProblem(String problem);

	/**
	 * Returns the parameter that can be used to gain the version of the solver when 
	 * executing it.
	 *       */
	public String getVersionParameter();
	/**
	 * Returns an array of all versions that are supported by KeY.
	 *     */
	public String[] getSupportedVersions();
	/**
	 * Returns the current version that is installed, if it has already been checked, otherwise null.
	 *    */
	public String getVersion();

    /**
     * Retrieve the version string without check for support.
     * Returns null if the solver is not installed.
     */
    public String getRawVersion();

	/**
	 * Returns whether the currently installed version is supported.
	 *     */
	public boolean isSupportedVersion();
	/**
	 * Checks for support and returns the result.
	 * */
	public boolean checkForSupport();
	/**
	 * returns true if and only if the support has been checked for the currently installed solver.
	 */
	public boolean supportHasBeenChecked();

   

	
	/**
     * Class for the Z3 solver. It makes use of the SMT2-format.
     */
    static public final SolverType Z3_SOLVER = new AbstractSolverType() {


            public String getDefaultSolverCommand() {
                return "z3";
                }

            public String getDefaultSolverParameters() {
                return "-in -smt2";
                }

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

            public String getVersionParameter() {
            	return "-version";
                }
           
            @Override
                public String getRawVersion () {
                    final String tmp = super.getRawVersion();
                    if (tmp==null) return null;
                    return tmp.substring(tmp.indexOf("version"));
                }

            public String[] getSupportedVersions() {
            	return new String[] {"version 3.2","version 4.1","version 4.3.0","version 4.3.1"};
                }

            public String[] getDelimiters() {
            	return new String [] {"\n","\r"};
                }

            public boolean supportsIfThenElse() {
                    return true;
                }

            @Override
            public SMTTranslator createTranslator(Services services) {
                    return new SmtLib2Translator(services,
                                    new Configuration(false,false));
            }


            @Override
            public String getInfo() {
            			return "";
//                    return "Z3 does not use quantifier elimination by default. This means for example that"
//                                    + " the following problem cannot be solved automatically by default:\n\n"
//                                    + "\\functions{\n"
//                                    + "\tint n;\n"
//                                    + "}\n\n"
//                                    + "\\problem{\n"
//                                    + "\t((\\forall int x;(x<=0 | x >= n+1)) & n >= 1)->false\n"
//                                    + "}"
//                                    + "\n\n"
//                                    + "You can activate quantifier elimination by appending QUANT_FM=true to"
//                                    + " the execution command.";
            }




			

    };

	/**
	 * Class for the Z3 solver. It makes use of the SMT2-format.
	 */
	static public final SolverType Z3_CE_SOLVER = new AbstractSolverType() {




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
			return "Z3_CE";
		}

		public String getVersionParameter() {
			return "-version";
		};

		public String[] getSupportedVersions() {
			return new String[] {"version 4.3.1"};
		};

		public String[] getDelimiters() {
			return new String [] {"\n","\r"};
		};

		public boolean supportsIfThenElse() {
			return true;
		};
		@Override
		public SMTTranslator createTranslator(Services services) {
			return new SmtLib2Translator(services,
					new Configuration(false,false));
		}


		@Override
		public String getInfo() {
			return "";
			//                        return "Z3 does not use quantifier elimination by default. This means for example that"
			//                                        + " the following problem cannot be solved automatically by default:\n\n"
			//                                        + "\\functions{\n"
			//                                        + "\tint n;\n"
			//                                        + "}\n\n"
			//                                        + "\\problem{\n"
			//                                        + "\t((\\forall int x;(x<=0 | x >= n+1)) & n >= 1)->false\n"
			//                                        + "}"
			//                                        + "\n\n"
			//                                        + "You can activate quantifier elimination by appending QUANT_FM=true to"
			//                                        + " the execution command.";
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
	    }

	    private boolean useNewVersion () {
	        final String solverVersion = getRawVersion();
	        return "version 2.4.1".equals(solverVersion);
	    }

	    @Override
	    public String getRawVersion () {
	        final String tmp = super.getRawVersion();
	        if (tmp==null) return null;
	        return tmp.substring(tmp.indexOf("version"));
	    }

	    @Override
	    public String getDefaultSolverParameters() {
	        // version 2.4.1 uses different parameters
	        if (useNewVersion())
	            return "-lang smt +model +interactive";
	        //                      return "-lang smt2 +model +interactive";
	        else
	            return "+lang smt +model +int";
	    }

	    public String[] getDelimiters() {
	        return new String [] {"CVC>","C>"};
	    }

	    public String[] getSupportedVersions() {
	        return new String[] {"version 2.2", "version 2.4.1"};
	    }

	    public String getVersionParameter() {
	        return "-version";
	    }

	    @Override
	    public SMTTranslator createTranslator(Services services) {
	        final Configuration conf = new Configuration(false, true);
	        //                    if (useNewVersion())
	        //                        return new SmtLib2Translator(services, conf);
	        //                    else
	        return new SmtLibTranslator(services,conf);
	    }

	    public boolean supportsIfThenElse() {
	        return true;
	    }

	    @Override
	    public String getInfo() {
	        return null;
	    }




	};
	
	/**
	 * CVC4 is the successor to CVC3.
	 * @author bruns
	 */
	static public final SolverType CVC4_SOLVER = new AbstractSolverType() {

	    // TODO move to AbstractSolverType?
        @Override
        public SMTSolver createSolver(SMTProblem problem,
                        SolverListener listener, Services services) {
            return new SMTSolverImplementation(problem, listener,
                            services, this);
        }

        @Override
        public String getName() {
            return "CVC4";
        }

        @Override
        public String getInfo() {
            // todo Auto-generated method stub
            return null;
        }

        @Override
        public String getDefaultSolverParameters() {
            return "--no-print-success -m --interactive --lang smt2";
        }

        @Override
        public String getDefaultSolverCommand() {
            return "cvc4";
        }

        @Override
        public SMTTranslator createTranslator(Services services) {
            final Configuration conf = new Configuration(false, true);
            return new SmtLib2Translator(services, conf);
        }

        @Override
        public String[] getDelimiters() {
            return new String[]{"CVC4>"};
        }

        @Override
        public boolean supportsIfThenElse() {
            return true;
        }

        @Override
        public String getVersionParameter() {
            return "--version";
        }

        @Override
        public String[] getSupportedVersions() {
            return new String[]{"version 1.3"};
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
		public SMTTranslator createTranslator(Services services) {
			return new SmtLibTranslator(services,
					new Configuration(true,true));
		}


		@Override
		public String getDefaultSolverCommand() {
			return "yices";
		}

		public String[] getDelimiters() {
			return new String [] {"\n","\r"};
                }

		@Override
		public String getDefaultSolverParameters() {
			return "-i -e -smt";
		}


		public String getVersionParameter() {
			return "--version";
                }

		public String[] getSupportedVersions() {
			return new String [] {"1.0.34"};
                }

		@Override
		public String getInfo() {
			return "Use the newest release of version 1.x instead of version 2. Yices 2 does not support the "
			+ "required logic AUFLIA.";
		}

		public boolean supportsIfThenElse() {
			return true;
		};




		public String modifyProblem(String problem) {
			return problem += "\n\n check\n";
				}

	};

	/**
	 * Class for the Simplify solver. It makes use of its own format.
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
		public SMTTranslator createTranslator(Services services) {
			return new SimplifyTranslator(services,
					new Configuration(false,true));
		}

		public String getDefaultSolverCommand() {
			return "simplify";
                }

		public String[] getSupportedVersions() {
			return new String []{"version 1.5.4"};
                }

            @Override
                public String getRawVersion () {
                    final String tmp = super.getRawVersion();
                    if (tmp==null) return null;
                    return tmp.substring(tmp.indexOf("version"));
                }

		public String[] getDelimiters() {
			return new String [] {">"};
                }

		public String getDefaultSolverParameters() {
			return "-print";
                }


		public String getVersionParameter() {
			return "-version";
                }


		@Override
		public String getInfo() {
			return "Simplify only supports integers within the interval [-2147483646,2147483646]=[-2^31+2,2^31-2].";
		}

		public boolean supportsIfThenElse() {
			return false;
                }


	};

}

abstract class AbstractSolverType implements SolverType {
	private boolean installWasChecked = false;
	private boolean isInstalled = false;
	private String solverParameters = getDefaultSolverParameters();
	private String solverCommand    = getDefaultSolverCommand();
	private String solverVersion    = "";
	private boolean isSupportedVersion = false;
	private boolean supportHasBeenChecked = false;


	








	



	 public static boolean isInstalled(String cmd) {


		 if (checkEnvVariable(cmd)) {
			 return true;
		 } else {

			 File file = new File(cmd);

			 return file.exists() && !file.isDirectory();

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

	 public boolean checkForSupport(){
		 if(!isInstalled){
			 return false;
		 }
		 supportHasBeenChecked = true;
            solverVersion = getRawVersion();
		 if(solverVersion == null){
			 solverVersion = "";
			 isSupportedVersion = false;
			 return false;
		 }
		 for(String supportedVersion : getSupportedVersions()){
			 if(solverVersion.indexOf(supportedVersion)>-1){
				 isSupportedVersion = true;
				 return true;
			 }
		 }
		 isSupportedVersion = false;
		 return false;
	 }

	 @Override
	 public boolean supportHasBeenChecked() {
		 return supportHasBeenChecked;
	 }

	 @Override
	 public boolean isSupportedVersion() {
		 return isSupportedVersion;
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
		 supportHasBeenChecked = false;
		 solverCommand = s;
	 }

	 @Override
	 public final String getSolverCommand() {
		 if(solverCommand == null || solverCommand.isEmpty()){
			 return getDefaultSolverCommand();
		 }
		 return solverCommand;
	 }

	 public String getVersion() {
		 return solverVersion;
		}

        public String getRawVersion() {
            if (isInstalled(true))
                return VersionChecker.INSTANCE.getVersionFor(getSolverCommand(),getVersionParameter());
            else return null;
	 }

	 public String toString() {
		 return getName();
	 }

	 @Override
	 public String modifyProblem(String problem) {
		 return problem;
	 }

}
