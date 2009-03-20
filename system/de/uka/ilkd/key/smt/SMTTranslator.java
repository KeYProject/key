//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                    Universitaet Koblenz-Landau, Germany
//                    Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;


public interface SMTTranslator {

    public static enum TERMPOSITION {ANTECEDENT, SUCCEDENT}
    
    /**
     * Translate a sequent.
     * @param sequent the sequent to translate.
     * @param services wrapper object for service attributes.
     * @return A StringBuffer representing the sequent in the given syntax.
     * @throws IllegalFormulaException if the sequent could not be translated.
     */
    public StringBuffer translate(Sequent sequent, Services services)
    		throws IllegalFormulaException;
    
    /**
     * Translates the given sequent into "Simplify" input syntax and adds
     * the resulting string to the StringBuffer sb.
     * 
     * @param sequent
     *                the Sequent which should be written in Simplify syntax
     */
    public StringBuffer translate(Sequent sequent,
	    boolean lightWeight, Services services)
	    throws IllegalFormulaException;

    /**
     * Translate s term into the given syntax.
     * @param t The term to translate.
     * @param services a service wrapper object.
     * @return A StringBuffer, representing the term in the given syntax.
     * @throws IllegalArgumentException if the term is not of type FORMULA or could not be translated.
     */
    public StringBuffer translate(Term t, Services services) 
    		throws IllegalFormulaException;
}
