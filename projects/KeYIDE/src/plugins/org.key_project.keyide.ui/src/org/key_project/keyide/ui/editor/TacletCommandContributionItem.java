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
import de.uka.ilkd.key.rule.TacletApp;


/**
 * A customized {@link CommandContributionItem} which contains a {@link TacletApp}, a {@link KeYMediator} and a {@link PosInSequent}.
 * 
 * @author Christoph Schneider, Niklas Bunzel, Stefan Käsdorf, Marco Drebing
 */
public class TacletCommandContributionItem extends CommandContributionItem {
   /**
    * The {@link Goal} at which to apply the rule.
    */
   private final Goal goal;
   
   /***
    * The {@link TacletApp} to apply.
    */
   private final TacletApp app;
   
   /**
    * The {@link UserInterfaceControl} to use.
    */
   private final UserInterfaceControl ui;
   
   /**
    * The {@link PosInSequent} to apply {@link TacletApp} on.
    */
   private final PosInSequent pos;
   
   /**
    * The constructor with the additional parameters.
    * @param contributionParameters - the {@link CommandContributionItemParameter}.
    * @param app - the {@link TacletApp}.
    * @param ui - the {@link UserInterfaceControl}.
    * @param pos - the {@link PosInSequent}.
    */
   public TacletCommandContributionItem(CommandContributionItemParameter contributionParameters, Goal goal, TacletApp app, UserInterfaceControl ui, PosInSequent pos) {
      super(contributionParameters);
      this.goal = goal;
      this.app = app;
      this.ui = ui;
      this.pos = pos;
   }
   
   /**
    * Returns the {@link TacletApp} to apply.
    * @return The {@link TacletApp} to apply.
    */
   public TacletApp getTacletApp() {
      return app;
   }
   
   /**
    * Returns the {@link UserInterfaceControl} to use.
    * @return The {@link KeYMediator} to use.
    */
   public UserInterfaceControl getUi() {
      return ui;
   }
   
   /**
    * Returns the {@link Goal} at which to apply the rule.
    * @return The {@link Goal} at which to apply the rule.
    */
   public Goal getGoal() {
      return goal;
   }

   /**
    * Returns the {@link PosInSequent} to apply {@link TacletApp} on.
    * @return The {@link PosInSequent} to apply {@link TacletApp} on.
    */
   public PosInSequent getPosInSequent() {
      return pos;
   }
}