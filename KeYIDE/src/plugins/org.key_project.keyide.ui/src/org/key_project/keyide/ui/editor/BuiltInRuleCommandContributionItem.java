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

package org.key_project.keyide.ui.editor;

import org.eclipse.ui.menus.CommandContributionItem;
import org.eclipse.ui.menus.CommandContributionItemParameter;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.BuiltInRule;

/**
 * A customized {@link CommandContributionItem} which contains a {@link BuiltInRule}, a {@link KeYMediator} and a {@link PosInSequent}.
 * 
 * @author Martin Hentschel
 */
public class BuiltInRuleCommandContributionItem extends CommandContributionItem {
   /**
    * The {@link Goal} at which to apply rule.
    */
   private final Goal goal;
   
   /***
    * The {@link BuiltInRule} to apply.
    */
   private final BuiltInRule rule;
   
   /**
    * The {@link UserInterfaceControl} to use.
    */
   private final UserInterfaceControl ui;
   
   /**
    * The {@link PosInSequent} to apply {@link BuiltInRule} on.
    */
   private final PosInSequent pos;
   
   /**
    * The constructor with the additional parameters.
    * @param contributionParameters - the {@link CommandContributionItemParameter}.
    * @param rule - the {@link BuiltInRule}.
    * @param goal - the {@link Goal}.
    * @param ui - the {@link UserInterfaceControl}.
    * @param pos - the {@link PosInSequent}.
    */
   public BuiltInRuleCommandContributionItem(CommandContributionItemParameter contributionParameters, Goal goal, BuiltInRule rule, UserInterfaceControl ui, PosInSequent pos) {
      super(contributionParameters);
      this.goal = goal;
      this.rule = rule;
      this.ui = ui;
      this.pos = pos;
   }
   
   /**
    * Returns the {@link BuiltInRule} to apply.
    * @return The {@link BuiltInRule} to apply.
    */
   public BuiltInRule getRule() {
      return rule;
   }
   
   /**
    * Returns the {@link UserInterfaceControl} to use.
    * @return The {@link UserInterfaceControl} to use.
    */
   public UserInterfaceControl getUi() {
      return ui;
   }
   
   /**
    * Returns the {@link PosInSequent} to apply {@link BuiltInRule} on.
    * @return The {@link PosInSequent} to apply {@link BuiltInRule} on.
    */
   public PosInSequent getPosInSequent() {
      return pos;
   }

   /**
    * Returns the {@link Goal}.
    * @return The {@link Goal}.
    */
   public Goal getGoal() {
      return goal;
   }
}