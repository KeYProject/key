//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                    Universitaet Koblenz-Landau, Germany
//                    Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.smt.taclettranslation;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.rule.Taclet;

/**
 * This interface provides the mechanism of translating taclets to formulae. The
 * resulting formulae can be used for example for building assumptions for
 * external proofers. CAUTION: The correctness of a single formula, i.d. the
 * universal validity, depends on the particular taclet.
 */
public interface TacletSetTranslation {

    /**
     * sets the set of taclets that should be translated. The taclets will be
     * translated not until calling <code>getTranslation</code>.
     * 
     * @param set
     *            the set of taclets that should be translated.
     */
    public void setTacletSet(ImmutableSet<Taclet> set);

    /**
     * Builds the translation of the taclets given by calling the method
     * <code>setTacletSet()</code>.
     * 
     * @return returns the resulting formulae of the taclets. Each formula of
     *         the resulting set is associated with one taclet.
     */
    public ImmutableList<TacletFormula> getTranslation();

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

    /**
     * Adds a new heuristic to the translation. Only taclets that contain one of
     * the added heuristics will be translated. If no heuristic was added every
     * taclet is being translated.
     * 
     * @param h
     *            The heuristic to be added.
     */
    public void addHeuristic(String h);

    /**
     * Removes a heuristic. It has no effect of the translation that is already
     * done, call <code>update</code> to renew the translation.
     * 
     * @param h
     *            the heuristic to be removed.
     * @return return <code>true</code> if the heuristic have been remove
     *         successfully, otherwise <code>false</code>.
     */
    public boolean removeHeursitic(String h);

}
