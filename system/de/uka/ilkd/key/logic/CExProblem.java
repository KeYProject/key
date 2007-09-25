// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.logic.ldt.ADT;
/**
 * This class contains a an ADT and a conjecture and is the input for the call to Mgtp.
 * The package de.uka.ilkd.key.counterexample uses this as input for the generation
 * of the counterexample calculus which is then given as input to Mgtp. CEx stands
 * for CounterExample
 *
 * @author Sonja Pieper
 * @verions 0.1, 07/08/01
 */

public class CExProblem {

    private ADT datatype;
    private Axiom conjecture;

    //@@@ the following 3 variables are maybe not necessary:
    //private Namespace sorts;
    //private Namespace functions;
    //private Namespace variables;

    /**
     * creates a new CExProblem, CEx stands for CounterExample
     *
     * @param dt the abstract data type with which you are working
     * @param conj the conjecture which you want to disprove
     */
    public CExProblem(ADT dt, Axiom conj){
	datatype = dt;
	conjecture = conj;
    }

    /**
     * constructor supposed to parse the necessary information
     * from the filename given as parameter. a and c are an
     * axiom and a conjecture for testing only now. @@@
     */
    /* public CExProblem(String filename, String a, String c){

       TacletForTests taclet = new TacletForTests();
       taclet.parse(filename);
       sorts = taclet.getSorts();
       functions = taclet.getFunctions();
       variables = taclet.getVariables();
       
       Axiom axiom = new Axiom(taclet.parseTerm(a)); //@@@
       
       String name = filename.substring(0,filename.indexOf('.')-1);
       System.out.println("Dies ist der Name des neuen ADTs: "+name); //debug
       datatype = new ADT(name);
       
       while(namespace!=null){
       datatype.addSort(sorts);
       }
       
       datatype.addAxiom(axiom);
       
       conjecture = new Axiom(taclet.parseTerm(c));
       
       }
    */


    /**
     * output of the object as a string
     *
     * @return the string representation of the object
     */
    public String toString(){
	return datatype.toString()+"\n\n"+conjecture.toString();
    }

    public ADT getAdt(){ return datatype; }
    public Axiom getConjecture(){ return conjecture; }

}
