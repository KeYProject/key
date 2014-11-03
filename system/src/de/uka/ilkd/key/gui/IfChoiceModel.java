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

package de.uka.ilkd.key.gui;

import java.util.Iterator;

import javax.swing.DefaultComboBoxModel;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.parser.KeYLexerF;
import de.uka.ilkd.key.parser.KeYParserF;
import de.uka.ilkd.key.parser.ParserMode;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.MissingInstantiationException;
import de.uka.ilkd.key.proof.SVInstantiationParserException;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.rule.IfFormulaInstDirect;
import de.uka.ilkd.key.rule.IfFormulaInstantiation;
import org.antlr.runtime.RecognitionException;


public class IfChoiceModel extends DefaultComboBoxModel {


    /**
     * 
     */
    private static final long serialVersionUID = -5388696072469119661L;
    private static final String manualText="Manual Input";
    private String manualInput;
    //    private RuleApp app;
    private final Term ifFma;


   /** namespaces (variables, functions, sorts, etc.) */
    private final NamespaceSet nss;
    private final AbbrevMap scm;
    private final Services services;


    public IfChoiceModel ( Term                         p_ifFma,
			   ImmutableList<IfFormulaInstantiation> p_candidates,
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
    

    public static Object[] createIfInsts ( ImmutableList<IfFormulaInstantiation> p_candidates ) {
	Object[]                         res = new Object [ p_candidates.size () ];
	Iterator<IfFormulaInstantiation> it  = p_candidates.iterator ();
	int                              i   = 0;

	while ( it.hasNext () )
	    res[i++] = it.next ();

	return res;
    }


    /** creates a new Termparser that parses the given string
     * @param s the String to parse 
     */
    private KeYParserF stringParser(String s) {
	return new KeYParserF(ParserMode.TERM,new KeYLexerF(s, "", services.getExceptionHandler()),
			      new Recoder2KeY(services,
					      nss),			      
			      services, nss, scm);
    }


    /** 
     * parses and returns the term encoded as string 's' 
     * @param s the String to parse 
     * @return the term encoded in 's' 
     * @throws org.antlr.runtime.RecognitionException In case an exceptions occurs during parse.
     */
    public Term parseFormula(String s) throws RecognitionException {
	KeYParserF p = stringParser(s);
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
            return (IfFormulaInstantiation) o;
        }
        try {
            if (manualInput == null || "".equals(manualInput)) {
                throw new MissingInstantiationException(
                        "'\\assumes'-formula: "
                        + ProofSaver.printAnything(ifFma, services), pos, -1, true);
            }

            return new IfFormulaInstDirect(new SequentFormula(parseFormula(manualInput)));
        } catch (RecognitionException e) {
            throw new SVInstantiationParserException(manualInput, pos, e.charPositionInLine,
                    "Problem occured parsing a manual input"
                    + " of an '\\assumes'-sequent.\n" + e.getMessage(), true);
        }
    }

}
