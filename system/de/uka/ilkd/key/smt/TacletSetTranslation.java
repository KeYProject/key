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

import java.util.Collection;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rule.Taclet;



/** This interface provides the mechanism of translating taclets to formulae.
 *  The resulting formulae can be used for example for building assumptions for external proofers.
 *  CAUTION: The correctness of a single formula, i.d. the universal validity, depends on the particular taclet.
 */
public interface TacletSetTranslation {
   
    /**
     * sets the set of taclets that should be translated. The taclets will be translated not until calling <code>getTranslation</code>.
     * @param set the set of taclets that should be translated.
     */
    public void setTacletSet(ImmutableSet<Taclet> set);
   
    /**
     * Builds the translation of the taclets given by calling the method <code>setTacletSet()</code>.
     * @return returns the resulting formulae of the taclets. Each formula of the resulting set is associated with one taclet.
     */
    public ImmutableList<TacletFormula> getTranslation();
    


}
