// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

// This file is part of KeY - Integrated Deductive Software Design
 // Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                          Universitaet Koblenz-Landau, Germany
//                          Chalmers University of Technology, Sweden
 //
 // The KeY system is protected by the GNU General Public License. 
 // See LICENSE.TXT for details.
 //
 //

package de.uka.ilkd.key.taclettranslation;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.rule.Taclet;

public interface SkeletonGenerator{
    public final static SkeletonGenerator DEFAULT_TACLET_TRANSLATOR =
            new DefaultTacletTranslator(); 
    
    /**
     * Override this method to introduce a translating mechanism for taclets.
     * @param t
     *            taclet to be translated.
     * @return returns the translation of the taclet.
     */
    public Term translate(Taclet t)
	    throws IllegalTacletException;
}


/**
 * Translates a taclet into a logical skeleton without instantiating
 * the schema variables. This must be done by the user of this class.
 */
abstract class AbstractSkeletonGenerator implements SkeletonGenerator {
     /**
      * Translates a sequent to a term by using the following translations rules:
      * T ==> D is translated to: And(T)->Or(D).<br>
      * And(s): conjunction between all formulae in set s. Or(s): disjunction
      * between all formulae in set s.
      * 
      * @param s
      *            The sequent to be translated.
      * @return the resulting term of the translation or <code>null</code> if
      *         both antecedent and succendent are empty.
      */
     protected Term translate(Sequent s) {
 	TermBuilder builder = TermBuilder.DF;

 	ImmutableList<Term> ante = getFormulaeOfSemisequent(s.antecedent());
 	ImmutableList<Term> succ = getFormulaeOfSemisequent(s.succedent());

 	if (ante.size() == 0 && succ.size() == 0)
 	    return null;
 	if (succ.size() == 0)
 	    return builder.not(builder.and(ante));
 	if (ante.size() == 0)
 	    return builder.or(succ);

 	return builder.imp(builder.and(ante), builder.or(succ));
     }


     /**
      * Collects all formulae of a semisequent in a set.
      * 
      * @param s
      *            Semisequent.
      * @return A list of all formulae of the semisequent <code>s </code>.
      */
     private ImmutableList<Term> getFormulaeOfSemisequent(Semisequent s) {
 	ImmutableList<Term> terms = ImmutableSLList.nil();
 	for (SequentFormula cf : s) {
 	    terms = terms.append(cf.formula());
 	}
 	return terms;

     }
}