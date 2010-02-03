// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.ListOfGoal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.reuse.ReusePoint;


interface ReuseListener extends KeYSelectionListener {

   

   



   
//remove RP with consumed goal
    void removeRPConsumedGoal(Goal usedGoal);


//add: old markers - new goals; call after removeRPConsumedMarker()
    void addRPOldMarkersNewGoals(ListOfGoal newGoals);


   
   
    void removeRPConsumedMarker(Node usedMarker);


//add RP: new markers - all goals
    void addRPNewMarkersAllGoals(Node usedMarker);
   
    boolean reusePossible();

   
    ReusePoint getBestReusePoint();

    void recomputeReuseTotal();
    
    void showState();

    void startShowingState();

    void showPreImage();

}
