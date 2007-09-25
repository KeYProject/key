// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.counterexample;

import de.uka.ilkd.key.logic.Axiom;
import de.uka.ilkd.key.logic.CExProblem;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ldt.ADT;
import de.uka.ilkd.key.logic.op.ConstructorFunction;
import de.uka.ilkd.key.logic.sort.ArrayOfGenSort;
import de.uka.ilkd.key.logic.sort.GenSort;
import de.uka.ilkd.key.rule.TacletForTests;

/**
 * TestProgramm zum Testen des CounterExample Packages
 * Achtung: sehr sehr gehackt, z.B. sind die Sorten in 
 * den Axiomen nicht dieselben wie die im ADT!!!!
 */

public class TestProgramm { 
    
    CExProblem problem;
    CounterExample gegenbeispiel;

    public TestProgramm(String filename, String ax, String conj){

	//parsing stuff:
	TacletForTests.parse(filename);
	Axiom axiom = new Axiom(TacletForTests.parseTerm(ax));
	Axiom conjecture = new Axiom(TacletForTests.parseTerm(conj));

	System.out.println("Axiom and conjecture successfully parsed.");

	//generating adt:
	ADT adt = new ADT(new Name("NatAdt"));

	GenSort nat = new GenSort(new Name("NatSorte"));
	GenSort[] gs = {nat};

	ArrayOfGenSort arg = new ArrayOfGenSort(gs);
	ConstructorFunction cnull = new ConstructorFunction(new Name("null"),nat,null);
	ConstructorFunction csucc = new ConstructorFunction(new Name("succ"),nat,arg);
	
	nat.addConstructor(cnull);
	nat.addConstructor(csucc);

	System.out.println("Sort nat successfully generated.");

	adt.addSort(nat);
	adt.addAxiom(axiom);
	
	System.out.println("Adt generation finished.");

	this.problem = new CExProblem(adt,conjecture);

	System.out.println("Starting CounterExample Generation");

	this.gegenbeispiel = new CounterExample(this.problem);
	
    }

    /**
     * Following: the test programm which should output the
     * results of the above functions if the programm does
     * not crash with a runtime exception beforehand.
     * first output should be the abstract data type and
     * second output should be the counterexample ...
     * while (not working) {
     *   if (output~(seems)~sensible) then { 'Hooray'; its = working }
     *   else { program some more }
     * }
     */

    public static void main(String[] args){

	System.out.println("Dies ist das CounterExample Testprogramm");

	TestProgramm test = new TestProgramm("natstack.txt",
					     args[0],
					     args[1]);

	System.out.println("Der Test ist gelaufen, Ausgabe folgt unten:\n"+
			   test.problem.toString()+"\n\n"+
			   test.gegenbeispiel.toString()+"\n\n"+
			   "Ende ....");
    }

}








