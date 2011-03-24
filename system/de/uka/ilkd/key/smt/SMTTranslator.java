// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;



public interface SMTTranslator {

    public static enum TERMPOSITION {ANTECEDENT, SUCCEDENT}
    
    
    
    /**
     * Translates a problem into the given syntax. The only difference to
     * <code>translate(Term t, Services services)</code> is that assumptions
     * will be added.
     * @param problem the problem to be translated.
     * @param services 
     * @return a StringBuffer representing the term in the given syntax.
     * @throws IllegalFormulaException
     */
    public StringBuffer translateProblem(Term problem, Services services,SMTSettings settings) 
           throws IllegalFormulaException;
    

    
    /**
     * Translate a term into the given syntax.
     * @param t The term to translate.
     * @param services a service wrapper object.
     * @return A StringBuffer, representing the term in the given syntax.
     * @throws IllegalArgumentException if the term is not of type FORMULA or could not be translated.
     */
    public StringBuffer translate(Term t, Services services, SMTSettings settings) 
    		throws IllegalFormulaException;

}
