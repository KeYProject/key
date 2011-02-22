////This file is part of KeY - Integrated Deductive Software Design
//
//package de.uka.ilkd.key.smt;
//
//import de.uka.ilkd.key.java.Services;
//
//
//
//public final class YicesSolver extends SMTSolverImplementation {
//
//    public static final String name = "Yices";
//    
//
//    public String name() {
//	return name;
//    }
//    
//    public YicesSolver(SMTProblem problem, SolverListener listener, Services services){
//	super(problem, listener, services);
//    }
//    
//    
//
//    @Override
//    protected String getExecutionCommand(String filename, String formula) {
//
//	//String toReturn = "yices -tc -smt " + filename;
//	//The following command tells yices to return a model if possible 
//	String toReturn = "yices -tc -e -smt " + filename;
//
//	return toReturn;
//    }
//
//    
//    public SMTSolverResult interpretAnswer(String input, String error, int val) {
//	if (val == 0) {
//	
//	    //no error occured
//	    //The commented out code works if no models (counterexamples) interpreted
////	    if (input.equals("unsat\n")) {
////		return SMTSolverResult.createValidResult(input);
////	    } else if (input.equals("sat\n")) {
////		return SMTSolverResult.createInvalidResult(input);
////	    } else {
////		return SMTSolverResult.createUnknownResult(input);
////	    }
//	    if (input.startsWith("unsat\n")) {
//		return SMTSolverResult.createValidResult(input,name());
//	    } else if (input.startsWith("sat\n")) {
//		return SMTSolverResult.createInvalidResult(input,name());
//	    } else {
//		return SMTSolverResult.createUnknownResult(input,name());
//	    }
//
//	} else {
//	    throw new IllegalResultException(error);
//	}
//	
//	
//    }
//    
//
//    @Override
//    public String getInfo() {
////       return "Use the newest release of version 1.x instead of version 2. Yices 2 does not support the " +
////       	       "required logic AUFLIA.";
//    }
//}
