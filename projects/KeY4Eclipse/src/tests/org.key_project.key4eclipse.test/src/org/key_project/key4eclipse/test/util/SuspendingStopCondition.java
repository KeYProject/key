/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.key4eclipse.test.util;

import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.gui.ApplyStrategy.IStopCondition;
import de.uka.ilkd.key.gui.ApplyStrategy.SingleRuleApplicationInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.IGoalChooser;
import de.uka.ilkd.key.proof.Proof;

/**
 * This {@link IStopCondition} can be used to block the the auto mode temporary.
 * @author Martin Hentschel
 */
public class SuspendingStopCondition implements IStopCondition {
   /**
    * {@code true} block the current {@link Thread}, {@code false} do not block current {@link Thread}.
    */
   private boolean sleep;
   
   /**
    * The maximal number of allowed rules.
    */
   private int maxRules;

   /**
    * The sleep time.
    */
   private int sleepTime;
   
   /**
    * Default constructor.
    */
   public SuspendingStopCondition() {
      this(false, 1000, 100);
   }
   
   /**
    * Constructor.
    * @param sleep {@code true} block the current {@link Thread}, {@code false} do not block current {@link Thread}.
    * @param maxRules  The maximal number of allowed rules.
    * @param sleepTime The sleep time.
    */
   public SuspendingStopCondition(boolean sleep, int maxRules, int sleepTime) {
      this.sleep = sleep;
      this.maxRules = maxRules;
      this.sleepTime = sleepTime;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int getMaximalWork(int maxApplications, long timeout, Proof proof, IGoalChooser goalChooser) {
      return 0;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isGoalAllowed(int maxApplications, long timeout, Proof proof, IGoalChooser goalChooser, long startTime, int countApplied, Goal goal) {
      if (sleep) {
         TestUtilsUtil.sleep(sleepTime);
      }
      return countApplied <= this.maxRules;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getGoalNotAllowedMessage(int maxApplications, long timeout, Proof proof, IGoalChooser goalChooser, long startTime, int countApplied, Goal goal) {
      return null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean shouldStop(int maxApplications, long timeout, Proof proof, IGoalChooser goalChooser, long startTime, int countApplied, SingleRuleApplicationInfo singleRuleApplicationInfo) {
      if (sleep) {
         TestUtilsUtil.sleep(sleepTime);
      }
      return countApplied > this.maxRules;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getStopMessage(int maxApplications, long timeout, Proof proof, IGoalChooser goalChooser, long startTime, int countApplied, SingleRuleApplicationInfo singleRuleApplicationInfo) {
      return null;
   }

   /**
    * Defines if the current {@link Thread} should be blocked or not.
    * @param sleep {@code true} block the current {@link Thread}, {@code false} do not block current {@link Thread}.
    */
   public void setSleep(boolean sleep) {
      this.sleep = sleep;
   }

   /**
    * Sets the maximal number of allowed rules.
    * @param maxRules The maximal number of allowed rules.
    */
   public void setMaxRules(int maxRules) {
      this.maxRules = maxRules;
   }
}