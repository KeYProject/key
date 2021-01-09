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

package de.uka.ilkd.key.smt;

import java.util.ArrayList;
import java.util.Collection;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;


/**
 * Classes that implement this interface provide a translation of
 * a KeY-problem into a specific format.
 *
 * Consider not implementing this interface directly, but to extend
 * the class {@link AbstractSMTTranslator}.
 */
public interface SMTTranslator {

    /**
     * Translates a problem into the given syntax. The only difference to
     * <code>translate(Term t, Services services)</code> is that assumptions
     * will be added.
     * @param sequent the sequent to be translated.
     * @param services
     * @return a representation of the term in the given syntax.
     * @throws IllegalFormulaException
     */
    public CharSequence translateProblem(Sequent sequent, Services services, SMTSettings settings)
           throws IllegalFormulaException;

}