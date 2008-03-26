// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.collection;

import de.uka.ilkd.key.proof.ListOfGoal;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * Wraps a ListOfGoal and a TacletApp in one object to allow returning them by one
 * function call.
 */
public class PairOfListOfGoalAndTacletApp {

    private Object[] pair = new Object[2];

    public PairOfListOfGoalAndTacletApp(ListOfGoal l, TacletApp t) {
        pair[0] = l;
        pair[1] = t;
    }

    public ListOfGoal getListOfGoal() {
        return (ListOfGoal) pair[0];
    }

    public TacletApp getTacletApp() {
        return (TacletApp) pair[1];
    }

}
