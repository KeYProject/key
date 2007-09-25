// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
//

package de.uka.ilkd.key.counterexample;

import de.uka.ilkd.key.logic.CExProblem;

/**
 * You can use this class to prove that a certain conjecture is wrong for an
 * abstract data type. On initialization of CounterExample you can enter the
 * problem which you want to test. Then you can generate the calculus and run
 * the ModelGeneration Software Mgtp to get the CounterExample data.
 * 
 * @author Sonja Pieper
 * @see de.uka.ilkd.key.logic.CExProblem
 * @version 1
 * @since 10.08.2001 
 */

public class CounterExample {

    private CExProblem problem;
    private Calculus calculus;
    private MgtpWrapper mgtp;
    private ModelRepresentation model;

    static Configuration config = new Configuration("max");

    public CounterExample(CExProblem cexproblem){
	problem = cexproblem;
	calculus = new ConjCalculus(problem);
        mgtp = new MgtpWrapper(calculus);
        model = new ModelRepresentation(mgtp.getProve());
    }

    public CExProblem getProblem() { return problem; }
    public String getProblemString() { return problem.toString(); }

    public Calculus getCalculus() { return calculus; }
    public String getCalculusString()    { return calculus.toString();}

    public ModelRepresentation getModel()   { return model; }
    public String getModelString()          { return model.toString(); }

    public String toString(){
	String ausgabe = "\n\nCounter interpretation for the conjecture:\n"+
	    (this.problem.getConjecture()).toString()+ "\n\n\n"+
	    "Resulting term evaluation:\n\n"+model.getTermeval()+"\n"+
	    "The above interpretation satisfies the axioms,\n"+
	    "if instantiated by constructor terms with less then "+
	    (config.domainmax+1)+" constructors.\n"+
	    "\nSummary:\n"+
	    "\nThe conjecture "+
	    (this.problem.getConjecture()).toString()+
	    "\n\nis violated by the following variable assignment:\n"+
	    model.getVars()+
	    "\nand by the following evaluation of conjecture subterms:\n\n"+
	    model.getSubterms();
	return ausgabe;
    }

    /**
     * This method allows to let the counter example generation proces
     * start for a second time, with a newly generated calculus etc.
     * might be useful after changing the configuration.
     */
    public void runAgain(){
	calculus = new ConjCalculus(problem);
        mgtp = new MgtpWrapper(calculus);
        model = new ModelRepresentation(mgtp.getProve());
    }
    
    public static void changeConfiguration(){ config.changeConfiguration(); }
   
}
