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


package de.uka.ilkd.key.taclettranslation.assumptions;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.taclettranslation.TacletFormula;

/**
 * This interface provides the mechanism of translating taclets to formulae. The
 * resulting formulae can be used for example for building assumptions for
 * external proofers. CAUTION: The correctness of a single formula, i.d. the
 * universal validity, depends on the particular taclet.
 */
public interface TacletSetTranslation {



    /**
     * Builds the translation of the taclets given by calling the method
     * <code>setTacletSet()</code>.
     * @param sorts this sorts are used for the instantiation of generic types.
     * @return returns the resulting formulae of the taclets. Each formula of
     *         the resulting set is associated with one taclet.
     */
    public ImmutableList<TacletFormula> getTranslation(ImmutableSet<Sort> sorts);

    /**
     * Returns all taclet that have not been translated. The reason can be got
     * by {@link TacletFormula#getStatus}.
     * 
     * @return a list of taclets.
     */
    public ImmutableList<TacletFormula> getNotTranslated();

    /**
     * Updates the translation, i.d. the given list of taclets is being
     * translated again.
     */
    public void update();



}
