// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.parser.ast;


import java.util.List;

import de.uka.ilkd.asmkey.util.ArrayUtil;
import de.uka.ilkd.asmkey.util.CollectionUtil;
import de.uka.ilkd.key.parser.Location;


/** AST node for taclets. This class represents the various kinds of
 * taclets (w/o if-sequent, condition, modifiers, etc).
 *
 * @author Hubert Schmid */

public final class AstTaclet extends AstNode {

    /** if-sequent if one exists or 'null'. */
    private final AstSequent ifSeq;

    /** find-term or 'null', if the find clause contains a sequent. */
    private final AstTerm term;

    /** find-sequent or 'null', if the find clause contains a term. */
    private final AstSequent sequent;

    /** List of variable conditions. i.e. List<AstCondition>. */
    private final List conds;

    /** List of taclet goals. i.e. List<AstGoal>. */
    private final List goals;

    /** List of taclet modifiers. i.e. List<AstTacletModifier>. */
    private final List modifiers;


    /** Creates a taclet with a find-term. The ifSeq may be 'null'. */
    public AstTaclet(Location location,
                     AstSequent ifSeq,
                     AstTerm term,
                     AstCondition[] conds,
                     AstGoal[] goals,
                     AstTacletModifier[] modifiers) {
        this(location, ifSeq, term, null, conds, goals, modifiers);
    }

    /** Creates a taclet with a find-sequent. The ifSeq may be 'null'. */
    public AstTaclet(Location location,
                     AstSequent ifSeq,
                     AstSequent sequent,
                     AstCondition[] conds,
                     AstGoal[] goals,
                     AstTacletModifier[] modifiers) {
        this(location, ifSeq, null, sequent, conds, goals, modifiers);
    }

    private AstTaclet(Location location,
                      AstSequent ifSeq,
                      AstTerm term,
                      AstSequent sequent,
                      AstCondition[] conds,
                      AstGoal[] goals,
                      AstTacletModifier[] modifiers) {
        super(location);
        this.ifSeq = ifSeq;
        this.term = term;
        this.sequent = sequent;
        this.conds = ArrayUtil.toList(conds);
        this.goals = ArrayUtil.toList(goals);
        this.modifiers = ArrayUtil.toList(modifiers);
    }


    /** Returns if-sequent of 'null', if no if-sequent exists. */
    public AstSequent getIfSeq() {
        return ifSeq;
    }

    /** Returns the find-term, or 'null' if the find-clause contains a
     * sequent. */
    public AstTerm getTerm() {
        return term;
    }

    /** Returns the find-sequent, or 'null' if the find-clause
     * contains a term. */
    public AstSequent getSequent() {
        return sequent;
    }

    /** Returns the list of variable conditions,
     * i.e. List<AstCondition>. */
    public List getConditions() {
        return conds;
    }

    /** Returns the list of taclet goals, i.e. List<AstGoal>. */
    public List getGoals() {
        return goals;
    }

    /** Returns the list of taclet modifiers,
     * i.e. List<AstTacletModifier>. */
    public List getModifiers() {
        return modifiers;
    }

    /** for debug only */
    public String toString() {
        return "[Taclet:ifSeq="
            + ifSeq
            + (term != null ? ",term=" + term : ",sequent=" + sequent)
            + ",goals="
            + CollectionUtil.toString(goals)
            + "]";
    }

}
