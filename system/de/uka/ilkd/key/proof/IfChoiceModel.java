// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof;

import java.io.StringReader;

import javax.swing.DefaultComboBoxModel;

import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.parser.KeYLexer;
import de.uka.ilkd.key.parser.KeYParser;
import de.uka.ilkd.key.parser.ParserMode;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.rule.IfFormulaInstDirect;
import de.uka.ilkd.key.rule.IfFormulaInstantiation;
import de.uka.ilkd.key.rule.IteratorOfIfFormulaInstantiation;
import de.uka.ilkd.key.rule.ListOfIfFormulaInstantiation;


public class IfChoiceModel extends DefaultComboBoxModel {


    private static final String manualText="Manual Input";
    private String manualInput;
    //    private RuleApp app;
    private Term ifFma;


   /** namespaces (variables, functions, sorts, etc.) */
    private NamespaceSet nss;
    private AbbrevMap scm;
    private Services services;


    public IfChoiceModel ( Term                         p_ifFma,
			   ListOfIfFormulaInstantiation p_candidates,
			   Services                     p_services,
			   NamespaceSet                 nss,
			   AbbrevMap                    scm) {
	super ( createIfInsts ( p_candidates ) );
	
	ifFma       = p_ifFma;
	services    = p_services;
	this.nss    = nss;
	this.scm    = scm;

	addElement(manualText);
	manualInput = "";
    }


    public String manualText() {
	return manualText;
    }

    public void setInput(String s) {
	manualInput = s;
    }

    public Term ifFma() {
	return ifFma;
    }
    

    public static Object[] createIfInsts ( ListOfIfFormulaInstantiation p_candidates ) {
	Object[]                         res = new Object [ p_candidates.size () ];
	IteratorOfIfFormulaInstantiation it  = p_candidates.iterator ();
	int                              i   = 0;

	while ( it.hasNext () )
	    res[i++] = it.next ();

	return res;
    }


    /** creates a new Termparser that parses the given string
     * @param s the String to parse 
     */
    private KeYParser stringParser(String s) {
	return new KeYParser(ParserMode.TERM,new KeYLexer(new StringReader(s),services.getExceptionHandler()),
			      "", TermFactory.DEFAULT, 
			      new Recoder2KeY(services,
					      nss),			      
			      services, nss, scm);
    }


    /** 
     * parses and returns the term encoded as string 's' 
     * @param s the String to parse 
     * @return the term encoded in 's' 
     */
    public Term parseFormula(String s) throws antlr.ANTLRException {
	KeYParser p = stringParser(s);
	return p.formula();
    }


    /**
     * @param pos int describes position of the if-sequent 
     *   (only required for error message)
     * @return the selected instantiation of the if sequent
     */
    public IfFormulaInstantiation getSelection(int pos) 
	throws SVInstantiationParserException, MissingInstantiationException {
	Object o = getSelectedItem();
	if (o != manualText) {
	    return (IfFormulaInstantiation)o;
	}
	try {
 	    if (manualInput == null || "".equals(manualInput)) {
		throw new MissingInstantiationException(
		    "'\\assumes'-formula: " + 
		    ProofSaver.printAnything(ifFma, services), pos+1, -1, true);
	    }

	    return new IfFormulaInstDirect ( new ConstrainedFormula ( parseFormula(manualInput),
								      Constraint.BOTTOM ) );
	} catch (antlr.RecognitionException are) {
 	    throw new SVInstantiationParserException
 		( manualInput, pos+are.getLine(), are.getColumn(), 
		  "Problem occured parsing a manual input"
 		  + " of an '\\assumes'-sequent.\n" +  are.getMessage(), true);
	} catch (antlr.ANTLRException e) {
 	    throw new SVInstantiationParserException
 		( manualInput, pos, -1, "Problem occured parsing a manual input"
 		  +" of an '\\assumes'-sequent.\n" +  e.getMessage(), true);
 	} 
    }

}
