// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.unittest.cogent;

import java.util.HashMap;

import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.NumberTranslation;
import de.uka.ilkd.key.unittest.ModelGenerator;

public class CogentTranslation{

    private Sequent sequent;
//    private ConstrainedSet cs;
    private HashMap<Term,String> array2pointer;
    private String arrayAxioms = "";
    private String boundaryAxioms = "";
    private int pointerCounter = 0;

    public CogentTranslation(Sequent sequent){
	this.sequent = sequent;
	array2pointer = new HashMap<Term,String>();
//	this.cs = cs;
    }

    protected String translate() throws CogentException{
	String ante = translate(sequent.antecedent(), true);
	String succ = translate(sequent.succedent(), false);
	return "!"+"("+arrayAxioms + boundaryAxioms + ante+") || ("+ succ +")";
    }

    public String translate(Semisequent ss, boolean ante) 
	throws CogentException{
	String junctor = ante ? " && " : " || ";
	String result = ante ? "1" : "0";
	for (int i = 0; i < ss.size(); i++) {
	    if(cogentizable(ss.get(i).formula())){
		try{
		    result += junctor+translate(ss.get(i).formula());
		}catch(UndefinedTermException e){
		    //do nothing - formula containing undefined term not added
		}catch(CogentException e){
		    //do nothing
		}
	    }
	}
	return result;
    }

    public boolean cogentizable(Term t){
	Operator op = t.op();	
	return !( ModelGenerator.containsImplicitAttr(t) || 
		  op == Op.ALL || op == Op.EX || (op instanceof Modality) ||
		  (op instanceof IUpdateOperator));
    }

    //convenience method
    public String translate(Term term) throws CogentException {
	return translate(term, true);
    }

    public String translate(Term term, 
			    boolean boundaryAxiom) throws CogentException {
	Operator op = term.op();
	if(boundaryAxiom && term.sort() != Sort.FORMULA){
	    boundaryAxioms += 
		"("+translate(term, false)+">=-2147483648) && ("+
		translate(term, false)+"<=2147483647) &&";
	}
	if (op == Op.NOT) {
	    return "(!"+translate(term.sub(0))+")";
	} else if (op == Op.AND) {
	    return "("+ translate(term.sub(0))+" && " + translate(term.sub(1))
		+ ")";
	} else if (op == Op.OR) {
	    return "("+ translate(term.sub(0))+" || " + 
		translate(term.sub(1))+ ")";
	} else if (op == Op.IMP) {
	    return "(!"+ translate(term.sub(0))+" || " + 
		translate(term.sub(1))+ ")";
	} else if (op == Op.EQV || op == Op.EQUALS) {
	    return "("+ translate(term.sub(0))+" == " + 
		translate(term.sub(1))+ ")";
	} else if (op == Op.TRUE) {
	    return "1";
	} else if (op == Op.FALSE) {
	    return "0";	    
	} else if (op instanceof AttributeOp) {
	    String attrName = ((AttributeOp) op).attribute().name().toString();
	    if(attrName.equals("length") && 
	       (term.sub(0).sort() instanceof ArraySort)){
		arrayAxioms += 
		    "("+translate(term.sub(0))+"."+attrName+">=0) &&";
	    }
	    return translate(term.sub(0))+"."+
		attrName.substring(attrName.lastIndexOf(":")+1);
	} else if(op instanceof ProgramVariable) {
	    String s = op.name().toString();
	    if(s.indexOf(":")!=-1){
		return s.substring(0, s.indexOf(":"))+
		    s.substring(s.indexOf(":")+2);
	    }
	    return s;
	} else if (op instanceof ArrayOp) {
	    String arrayName = (String) array2pointer.get(term);
	    if(arrayName == null){
		arrayName = "_arrayPlaceHolder"+(pointerCounter++);
		array2pointer.put(term, arrayName);
	    }
	    createArrayAxiom(arrayName, term);
	    return "*"+arrayName;
	} else if(term.op() == Op.NULL){
	    return "null";
	} else if(op instanceof RigidFunction && term.arity()==0 && 
		  op.name().toString().indexOf("undef(")==-1 &&
		  !(op instanceof Metavariable)){
	    if(op.name().toString().equals("int_Min")){
		return "-2147483648";
	    }else if(op.name().toString().equals("int_Max")){
		return "2147483647";
	    }else if(op.name().toString().equals("short_Min")){
		return "-32768";
	    }else if(op.name().toString().equals("short_Max")){
		return "32767";
	    }else if(op.name().toString().equals("byte_Min")){
		return "-128";
	    }else if(op.name().toString().equals("byte_Max")){
		return "127";
	    }else if(op.name().toString().equals("char_Min")){
		return "0";
	    }else if(op.name().toString().equals("char_Max")){
		return "65535";
	    }else{
		return op.name().toString();
	    }
	} else if (op instanceof Function) {
	    String name = op.name().toString().intern();
	    if (name.equals("add") || name.equals("jadd")) {
		return "("+ translate(term.sub(0))+" + " 
		    + translate(term.sub(1))+ ")";
	    } else if (name.equals("sub") || name.equals("jsub") || 
		       name.equals("subJint")) {
		return "("+ translate(term.sub(0))+" - " + 
		    translate(term.sub(1))+ ")";
	    } else if (name.equals("neg") || name.equals("jneg")
			   || name.equals("negJint")) {
		return "-"+ translate(term.sub(0));
	    } else if (name.equals("mul") || name.equals("jmul") 
		       || name.equals("mulJint")) {
		return "("+ translate(term.sub(0))+" * " 
		    + translate(term.sub(1))+ ")";		
	    } else if (name.equals("div") || name.equals("jdiv") 
		       || name.equals("divJint")) {
		return "("+ translate(term.sub(0))+" / " 
		    + translate(term.sub(1))+ ")";
	    } else if (name.equals("mod") || name.equals("jmod") 
		       || name.equals("modJint")) {
		return "("+ translate(term.sub(0))+" % " 
		    + translate(term.sub(1))+ ")";
	    } else if (name.equals("lt")) {
		return "("+ translate(term.sub(0))+" < " 
		    + translate(term.sub(1))+ ")";
	    } else if (name.equals("gt")) {
		return "("+ translate(term.sub(0))+" > " 
		    + translate(term.sub(1))+ ")";
	    } else if (name.equals("leq")) {
		return "("+ translate(term.sub(0))+" <= " 
		    + translate(term.sub(1))+ ")";
	    } else if (name.equals("geq")) {
		return "("+ translate(term.sub(0))+" >= " 
		    + translate(term.sub(1))+ ")";
	    } else if (name.equals("undef")) {
		throw new UndefinedTermException(term);
	    } else if (name.equals("Z") || name.equals("C")) {
		return NumberTranslation.translate(term.sub(0)).toString();
	    }
	}
	throw new CogentException("Term "+term +" not translatable to "+
				  "Congent input syntax.");
    }

    private void createArrayAxiom(String arrayName, Term term) 
	throws CogentException {
	arrayAxioms += "("+arrayName+"=="+translate(term.sub(0))+" + "+
	    translate(term.sub(1))+") &&";
    }
}
