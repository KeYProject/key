// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.proof;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.util.Vector;

import de.uka.ilkd.asmkey.gui.ProverFrame;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.gui.ProofSettings;
import de.uka.ilkd.key.gui.notification.events.GeneralFailureEvent;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.IteratorOfNode;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofSaver;
import de.uka.ilkd.key.rule.*;

/**
 * This class is responsible for saving the proofs
 * of asmkey.
 * 
 * @see ProofSaver
 * @see AsmProofLoader
 * @author Stanislas Nanchen
 */
public class AsmProofSaver extends ProofSaver {

    private AsmProof proof;
    private File file;
    private LogicPrinter printer;
    
    public AsmProofSaver(File file, AsmProof proof) {
	super(ProverFrame.getInstance(), file.getAbsolutePath());
	this.file = file;
	this.proof = proof;
    }

    public StringBuffer writeLog(Proof p){
	StringBuffer logstr=new StringBuffer();
	//Advance the Logentries
	if(p.userLog==null)
	    p.userLog = new Vector();
	if(p.keyVersionLog==null)
	    p.keyVersionLog = new Vector();
	p.userLog.add(System.getProperty("user.name"));
	p.keyVersionLog.add(Main.getInstance().getPrcsVersion());
	int s = p.userLog.size();
	for(int i=0; i<s; i++){
	    /*        logstr.append("(log (number "+i+") (user "+
		      p.userLog.elementAt(i)+" ) (keyVersion "+
		      p.keyVersionLog.elementAt(i)+"))\n");
	    */
	    logstr.append("(keyLog \""+i+"\" (keyUser \""+
			  p.userLog.elementAt(i)+"\" ) (keyVersion \""+
			  p.keyVersionLog.elementAt(i)+"\"))\n");
	}
	return logstr;
    }
    
    public String writeSettings(ProofSettings ps){
    	return new String ("settings {\n\""+ps.settingsToString()+"\"\n}\n");
    }
    
    public String save() {
	String errorMsg = null;
	FileOutputStream fos = null;
	PrintStream ps = null;
	
	try {
	    fos = new FileOutputStream(file);
	    ps = new PrintStream(fos);
	    String closed = proof.closed()?"TRUE":"FALSE";
	    
	    
	    Sequent problemSeq = proof.root().sequent();
	    printer = createLogicPrinter();
	    
	    //ps.println(writeSettings(proof.getSettings()));
	    ps.println("meta {");
	    ps.print("header=\"");
	    ps.print(proof.header());
	    ps.println("\"");
	    ps.println("name=" + proof.name());
	    ps.println("closed=" + closed);
	    ps.println("}\n");
	    ps.println("problem {");
	    printer.printSemisequent(problemSeq.succedent());
	    ps.println(printer.result());
	    ps.println("}\n");
	    //                ps.println(mediator.sort_ns());
	    ps.println("proof {");
	    ps.println(writeLog(proof));
	    ps.println(node2Proof(proof.root()));
	    ps.println("}");
	} catch (IOException ioe) {
	    errorMsg = "Could not save \n"+filename+".\n";
	    errorMsg += ioe.toString();	    
	} catch (NullPointerException npe) {
	    errorMsg = "Could not save \n"+filename+"\n";
	    errorMsg += "No proof present?";
	    npe.printStackTrace();
	} catch (Exception e) {
	    errorMsg = e.toString();
	    e.printStackTrace();
	} finally {
	    try {
		if (fos != null) fos.close();
	    } catch (IOException ioe) {
		mediator.notify(new GeneralFailureEvent(ioe.toString()));
	    }          
	}	  
	return errorMsg; // null if success
    }
    
    
    
    private StringBuffer collectProof(Node node, String prefix, 
				      StringBuffer tree) {       
	
	RuleApp appliedRuleApp = node.getAppliedRuleApp();
	if (appliedRuleApp == null && (proof.getGoal(node)!=null)) { // open goal
	    tree.append(prefix); 
	    tree.append("(opengoal \"");
	    LogicPrinter logicPrinter = createLogicPrinter();
	    
	    logicPrinter.printSequent(node.sequent());
	    tree.append(printer.result().toString().replace('\n',' '));
	    tree.append("\")\n");
	    return tree;
	}
	
	IteratorOfNode childrenIt = node.childrenIterator(); 
	
	
	if (appliedRuleApp instanceof TacletApp) {
	    tree.append(prefix); 
         tree.append("(rule \"");
         tree.append(appliedRuleApp.rule().name());	
         tree.append("\"");
         tree.append(posInOccurrence2Proof(node.sequent(), 
                 appliedRuleApp.posInOccurrence()));
         tree.append(getInteresting(((TacletApp)appliedRuleApp).instantiations()));
         ListOfIfFormulaInstantiation l =
	     ((TacletApp)appliedRuleApp).ifFormulaInstantiations();
         if (l != null) tree.append(ifFormulaInsts(node, l));
         tree.append("");
         tree.append(")\n");
	}
	
	if (appliedRuleApp instanceof BuiltInRuleApp) {
	    tree.append(prefix); 
	    tree.append("(builtin \"");
	    tree.append(appliedRuleApp.rule().name().toString());
	    tree.append("\"");
	    tree.append(posInOccurrence2Proof(node.sequent(), 
                    appliedRuleApp.posInOccurrence()));
	    tree.append(")\n");
	}
	
	if (node.childrenCount() == 0) return tree;
	if (node.childrenCount() == 1) 
	    collectProof(childrenIt.next(), prefix, tree);
	else
	 while (childrenIt.hasNext()) {
	     Node child = childrenIt.next();
	     tree.append(prefix);
	     tree.append("(branch \""+child.getNodeInfo().getBranchLabel()+"\"\n");
	     collectProof(child, prefix+"   ", tree);
            tree.append(prefix+")\n");
	 }

	return tree;
    }
    
    
    public String node2Proof(Node node) {
	StringBuffer tree=new StringBuffer();
	String s = "(branch \"dummy ID\"\n"+collectProof(node, "",tree)+")\n"; 
	return s;
    }
    
    
    public String posInOccurrence2Proof(Sequent seq, PosInOccurrence pos) {
	if (pos == null) return "";
	return " (formula \""+seq.formulaNumberInSequent(pos.isInAntec(),
                pos.constrainedFormula())+"\")"+
	    posInTerm2Proof(pos.posInTerm());
    }
    
    
    public String posInTerm2Proof(PosInTerm pos) {
	if (pos == PosInTerm.TOP_LEVEL) return "";
	String s = " (term \"";
	String list = pos.integerList(pos.reverseIterator()); // cheaper to read in
	s = s + list.substring(1,list.length()-1); // chop off "[" and "]"
	s = s + "\")";
	return s;
    }
    
    
    public String ifFormulaInsts(Node node, ListOfIfFormulaInstantiation l) {
	String s ="";
	IteratorOfIfFormulaInstantiation it = l.iterator();
	while (it.hasNext()) {
	    IfFormulaInstantiation iff = it.next();
	    if (iff instanceof IfFormulaInstSeq) {
		ConstrainedFormula f = iff.getConstrainedFormula();
		s+= " (ifseqformula \"" + 
		    node.sequent().formulaNumberInSequent(
							  ((IfFormulaInstSeq)iff).inAntec(),f) + 
		    "\")";
	    }
	    else
		if (iff instanceof IfFormulaInstDirect) {
		    throw new RuntimeException("IfFormulaInstDirect not yet supported");
		}
		else throw new RuntimeException("Unknown If-Seq-Formula type");
	}
	return s;
    }
    
    
    public static String printProgramElement(ProgramElement pe) {
	java.io.StringWriter sw = new java.io.StringWriter();
	ProgramPrinter prgPrinter = new ProgramPrinter(sw);
	try{
	    pe.prettyPrint(prgPrinter);
	} catch(IOException ioe) {System.err.println(ioe);}
	return sw.toString();
    }
    
    
    public static StringBuffer printTerm(Term t) {
	StringBuffer result;
	LogicPrinter logicPrinter = createLogicPrinter();
	try {
	    logicPrinter.printTerm(t);
	} catch(IOException ioe) {
	    System.err.println(ioe);
	}
	result = logicPrinter.result();
	if (result.charAt(result.length()-1) == '\n')
	    result.deleteCharAt(result.length()-1);
	return result;
    }
    
    private static LogicPrinter createLogicPrinter() {
	return new LogicPrinter(new ProgramPrinter(null), 
	                        NotationInfo.createInstance(), 
	                        null,
	                        true);
    }
}
