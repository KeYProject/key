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
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.smt.AbstractSMTTranslator.Configuration;
import de.uka.ilkd.key.smt.newsmt2.ModularSMTLib2Translator;


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


            @Override
            public String getDefaultSolverCommand() {
                return "z3";
                }

            @Override
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
                    return "Z3 (Legacy Translation)";
            }

            @Override
            public String getVersionParameter() {
            	return "-version";
                }

            @Override
                public String getRawVersion () {
                    final String tmp = super.getRawVersion();
                    if (tmp==null) {
                        return null;
                    }
                    return tmp.substring(tmp.indexOf("version"));
                }

            @Override
            public String[] getSupportedVersions() {
            	return new String[] {"version 3.2","version 4.1","version 4.3.0","version 4.3.1"};
                }

            @Override
            public String[] getDelimiters() {
            	return new String [] {"\n","\r"};
                }

            @Override
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
	 * Z3 with new modular translator
	 */
	static public final SolverType Z3_NEW_TL_SOLVER = new AbstractSolverType() {


		@Override
		public String getDefaultSolverCommand() {
			return "z3";
		}

		@Override
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

		@Override
		public String getVersionParameter() {
			return "-version";
		}

		@Override
		public String getRawVersion() {
			final String tmp = super.getRawVersion();
			if (tmp == null) {
				return null;
			}
			return tmp.substring(tmp.indexOf("version"));
		}

		@Override
		public String[] getSupportedVersions() {
			return new String[]{"version 3.2", "version 4.1", "version 4.3.0", "version 4.3.1", "version 4.8.8", "version 4.8.9", "version 4.8.10", "version 4.8.11", "version 4.8.12"};
		}

		@Override
		public String[] getDelimiters() {
			return new String[]{"\n", "\r"};
		}

		@Override
		public boolean supportsIfThenElse() {
			return true;
		}

		@Override
		public SMTTranslator createTranslator(Services services) {
			return new ModularSMTLib2Translator();
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




		@Override
        public String getDefaultSolverCommand() {
			return "z3";
		};

		@Override
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

		@Override
        public String getVersionParameter() {
			return "-version";
		};

		@Override
        public String[] getSupportedVersions() {
			return new String[] {"version 4.3.1"};
		};

		@Override
        public String[] getDelimiters() {
			return new String [] {"\n","\r"};
		};

		@Override
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
            return "CVC4 (Legacy Translation)";
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
	 * CVC4 with the new translation
	 */
	static public final SolverType CVC4_NEW_TL_SOLVER = new AbstractSolverType() {

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
            return new ModularSMTLib2Translator();
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
            return new String[]{"version 1.3", "version 1.7", "version 1.8"};
        }

	};

	public static List<SolverType> ALL_SOLVERS =
                Collections.unmodifiableList(Arrays.asList(
                        Z3_SOLVER,
                        CVC4_NEW_TL_SOLVER,
                        CVC4_SOLVER
                        ));
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
	 @Override
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
		 String path = System.getenv("PATH");

		 String[] res = path.split(File.pathSeparator);
		 for (String s : res) {
			 File file = new File(s + File.separator + cmd);
			 if (file.exists()) {
				 return true;
			 }
		 }

		 return false;

	 }

	 @Override
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

	 @Override
    public String getSolverParameters() {
		 if(solverParameters == null){
			 return getDefaultSolverParameters();
		 }
		 return solverParameters;
	 }

	 @Override
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

	 @Override
    public String getVersion() {
		 return solverVersion;
		}

        @Override
        public String getRawVersion() {
            if (isInstalled(true)) {
                return VersionChecker.INSTANCE.getVersionFor(getSolverCommand(),getVersionParameter());
            } else {
                return null;
            }
	 }

	 @Override
    public String toString() {
		 return getName();
	 }

	 @Override
	 public String modifyProblem(String problem) {
		 return problem;
	 }

}
