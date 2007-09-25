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

//import mgtp.*;

/**
 * This class calls the parser of Mgtp with the generated Calculus.
 * After the parser has processed the calculus, the theorem prover
 * is called and the returned model is then further processed
 * and written to the 'result' attribute. Most of the code is copied from
 * the Mgtp Class, so a new version of Mgtp might make changes necessary.
 * 
 * !!! I have not yet implemented any method to read the prove mgtp writes
 * to stdout!!!
 *
 * @author Sonja Pieper
 * @version 2.1
 * @since August 2000
 */

public class MgtpWrapper {//extends MGTP {

    private String parserInput;
    private String result;

    /**
     * Creates a new MgtpWrapper. All the initializations which are done in
     * the classbody of Mgtp are here done in the constructor.
     * Those parts of the code are mostly copied to make things easier to use.
     *
     * @param calc the constructor receives the previously generated calculus
     */

    MgtpWrapper(Calculus calc){

	parserInput = calc.toString();

	//	MGTP.mgtp = this;
	//setupOptions(mgtp.args);
	//------------------begin copied mgtp code--------------------------
	/* @@@ achtung mgtp code ist derzeit auskommentiert!
	   this.ac = new ACell();
	   
	   this.pModel=false;
	   this.nModel=false;
	   this.pdlF=DList.NIL; this.pdlL=DList.NIL; this.pdlnF=DList.NIL;
	   this.ndlF=DList.NIL; this.ndlL=DList.NIL; this.ndlnF=DList.NIL;
	   this.mdlF=DList.NIL; this.mdlL=DList.NIL; this.mdlnF=DList.NIL;
	   
	   this.closed=false; // R.H. 98.08.15
	   this.rll=RDlList.NIL;
	   this.rjl=RDjList.NIL;
	*/
	//------------------end  copied mgtp code--------------------------
    }

    /**
     * This function first calls the parser of MGTP with the generated calculus
     * and afterwards the prover is started. The MGTP output is written to the
     * attribute <code>result</code>.
     */
    private void runMgtp(){

	//------------------begin copied mgtp code--------------------------
	/* @@@ achtung mgtp code ist auskommentiert!
	   //mgtp copyright notice:
	   System.out.println("JavaCMGTP Version 32gR99.04.09 9-Apr-1999");
	   System.out.println("Copyright (c) 1997-1999 Kyushu University");
	   
	   mgtp=(selectMin ? new MGTPpickupMin() : mgtp );
	   
	   java.io.StringReader fis = new java.io.StringReader(generatedCalculus);
	   probName = "natstack";
	   parser=new MGTPParser(fis);
	   parser.mgtp = this;
	   time=System.currentTimeMillis();
	   if (!parser.parse(mgtp)) return;
	   time=System.currentTimeMillis()-time;
	   System.out.println("Parsing time: "+time+" msec");
	   
	   if (verbose) {
	   System.out.println("\n"
	   +"Positive clause(s):\n"+mgtp.posCls
	   +"Negative clause(s):\n"+mgtp.negCls
	   +"Cont. clause(s):\n"+mgtp.cntCls
	   +"Mixed clause(s):\n"+mgtp.mixCls);
	   }
	   
	   System.out.println("Proving . . .");
	   time=System.currentTimeMillis();
	   mgtp.init();
	   mgtp.posCls.first.cjmCL(null);
	   mgtp.prove(); //@@@ missing some kind of stdout readout to process info!
	   time=System.currentTimeMillis()-time;
	*/
	//------------------end copied mgtp code--------------------------

    }

	public String getProve(){
        this.runMgtp();
		return result; //@@@ see runMgtp() not yet done need stdout readout!
    }

	public boolean foundModel(){
	    //@@@ not really useful now!!!
	    return true; //mgtp.sat;
    }

    /**
     * Output of several mgtp statistics as number of models, branches, atoms
     * and of course if the problem is SAT or UNSAT.
     * @return A string representation of the above statistics.
     */
    public String getStats(){
	return "No Stats available right now!";
	/* @@@ auskommentierter mgtp code
	   return  "Number of models: "+mgtp.models+"\n"+
	   "Number of failed branches: "+mgtp.failedBranches+"\n"+
	   "Number of total branches: "+mgtp.branches+"\n"+
	   "Number of total atoms: "+mgtp.atoms+"\n"+
	   (mgtp.sat? "SAT": "UNSAT")+
	   "\nProving time: "+time+" msec\n";
	*/
    }

    

}














