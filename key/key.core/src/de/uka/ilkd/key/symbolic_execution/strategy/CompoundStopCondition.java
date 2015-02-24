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

package de.uka.ilkd.key.symbolic_execution.strategy;

import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.proof.ApplyStrategy;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.IGoalChooser;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ApplyStrategy.IStopCondition;
import de.uka.ilkd.key.proof.ApplyStrategy.SingleRuleApplicationInfo;

/**
 * This {@link IStopCondition} contains other {@link IStopCondition} as
 * children and stops the auto mode if at least on of its children force it.
 * @author Martin Hentschel
 */
public class CompoundStopCondition implements IStopCondition {
   /**
    * The child {@link IStopCondition}s to use.
    */
   private List<IStopCondition> children = new LinkedList<ApplyStrategy.IStopCondition>();
   
   /**
    * The last {@link IStopCondition} treated in {@link #isGoalAllowed(ApplyStrategy, int, long, Proof, IGoalChooser, long, int, Goal)}
    * which will provide the reason via {@link #getGoalNotAllowedMessage(ApplyStrategy, int, long, Proof, IGoalChooser, long, int, Goal)}.
    */
   private IStopCondition lastGoalAllowedChild;
   
   /**
    * The last {@link IStopCondition} treated in {@link #shouldStop(ApplyStrategy, int, long, Proof, IGoalChooser, long, int, SingleRuleApplicationInfo)}
    * which will provide the reason via {@link #getStopMessage(ApplyStrategy, int, long, Proof, IGoalChooser, long, int, SingleRuleApplicationInfo)}.
    */
   private IStopCondition lastShouldStopChild;

   /**
    * Constructor.
    * @param children The child {@link IStopCondition}s to use.
    */
   public CompoundStopCondition(IStopCondition... children) {
      Collections.addAll(this.children, children);
   }
   
   /**
    * Adds new child {@link IStopCondition}s.
    * @param children The child {@link IStopCondition}s to use.
    */
   public void addChildren(IStopCondition... children) {
      Collections.addAll(this.children, children);
   }
   
   public void removeChild(IStopCondition child){
      children.remove(child);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int getMaximalWork(int maxApplications, 
                             long timeout, 
                             Proof proof, 
                             IGoalChooser goalChooser) {
      // Get maximal work on each child because they might use this method for initialization purpose.
      for (IStopCondition child : children) {
         child.getMaximalWork(maxApplications, timeout, proof, goalChooser);
      }
      lastGoalAllowedChild = null;
      lastShouldStopChild = null;
      return 0;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isGoalAllowed(int maxApplications, 
                                long timeout, 
                                Proof proof, 
                                IGoalChooser goalChooser, 
                                long startTime, 
                                int countApplied, 
                                Goal goal) {
      boolean allowed = true;
      Iterator<IStopCondition> childIter = children.iterator();
      while (allowed && childIter.hasNext()) {
         lastGoalAllowedChild = childIter.next();
         allowed = lastGoalAllowedChild.isGoalAllowed(maxApplications, timeout, proof, goalChooser, startTime, countApplied, goal);
      }
      return allowed;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getGoalNotAllowedMessage(int maxApplications, 
                                          long timeout, 
                                          Proof proof, 
                                          IGoalChooser goalChooser, 
                                          long startTime, 
                                          int countApplied, 
                                          Goal goal) {
      return lastGoalAllowedChild != null ?
             lastGoalAllowedChild.getGoalNotAllowedMessage(maxApplications, timeout, proof, goalChooser, startTime, countApplied, goal) :
             null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean shouldStop(int maxApplications, 
                             long timeout, 
                             Proof proof, 
                             IGoalChooser goalChooser, 
                             long startTime, 
                             int countApplied, 
                             SingleRuleApplicationInfo singleRuleApplicationInfo) {
      boolean stop = false;
      Iterator<IStopCondition> childIter = children.iterator();
      while (!stop && childIter.hasNext()) {
         lastShouldStopChild = childIter.next();
         stop = lastShouldStopChild.shouldStop(maxApplications, timeout, proof, goalChooser, startTime, countApplied, singleRuleApplicationInfo);
      }
      return stop;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getStopMessage(int maxApplications, 
                                long timeout, 
                                Proof proof, 
                                IGoalChooser goalChooser, 
                                long startTime, 
                                int countApplied, 
                                SingleRuleApplicationInfo singleRuleApplicationInfo) {
      return lastShouldStopChild != null ?
             lastShouldStopChild.getStopMessage(maxApplications, timeout, proof, goalChooser, startTime, countApplied, singleRuleApplicationInfo) :
             null;
   }

   public List<IStopCondition> getChildren() {
      return children;
   }
}