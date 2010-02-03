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

public class ReuseListenerDummy implements ReuseListener {

   


   
//remove RP with consumed goal
   public void removeRPConsumedGoal(Goal usedGoal) {
   }


//add: old markers - new goals; call after removeRPConsumedMarker()
   public void addRPOldMarkersNewGoals(ListOfGoal newGoals) {
   }


   
   
   public void removeRPConsumedMarker(Node usedMarker) {
   }


//add RP: new markers - all goals
   public void addRPNewMarkersAllGoals(Node usedMarker) {
   }
   
   public boolean reusePossible() {
       return false;
   }

   
   public ReusePoint getBestReusePoint() {
       return null;
   }



   public void selectedNodeChanged(KeYSelectionEvent e) {
   }
 
   public void selectedProofChanged(KeYSelectionEvent e) {
   }
   
   public void recomputeReuseTotal() {
   }
   
   public void showState() {
   }
   
   public void startShowingState() {
   }
   
   public void showPreImage() {
   }

}
