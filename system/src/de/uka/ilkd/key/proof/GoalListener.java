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

package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.logic.SequentChangeInfo;

/** interface to be implemented by a goal listener */
public interface GoalListener {

    /** 
     * informs the listener about a change that occured to the sequent of goal
     */
    void sequentChanged(Goal source, SequentChangeInfo sci);


    /**
     * Informs the listener that the given goal <code>source</code>
     * has been replaced by the goals <code>newGoals</code> (note that
     * <code>source</code> may be an element of
     * <code>newGoals</code>). The nodes of <code>newGoals</code> are
     * children of the node <code>parent</code>
     */
    void goalReplaced(Goal source, Node parent, ImmutableList<Goal> newGoals);
}