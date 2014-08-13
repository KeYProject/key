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

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.rule.BuiltInRule;

/**
 * A customized {@link CommandContributionItem} which contains a {@link BuiltInRule}, a {@link KeYMediator} and a {@link PosInSequent}.
 * 
 * @author Martin Hentschel
 */
public class BuiltInRuleCommandContributionItem extends CommandContributionItem {
   /***
    * The {@link BuiltInRule} to apply.
    */
   private final BuiltInRule rule;
   
   /**
    * The {@link KeYMediator} to use.
    */
   private final KeYMediator mediator;
   
   /**
    * The {@link PosInSequent} to apply {@link BuiltInRule} on.
    */
   private final PosInSequent pos;
   
   /**
    * The constructor with the additional parameters.
    * @param contributionParameters - the {@link CommandContributionItemParameter}.
    * @param rule - the {@link BuiltInRule}.
    * @param mediator - the {@link KeYMediator}.
    * @param pos - the {@link PosInSequent}.
    */
   public BuiltInRuleCommandContributionItem(CommandContributionItemParameter contributionParameters, BuiltInRule rule, KeYMediator mediator, PosInSequent pos) {
      super(contributionParameters);
      this.rule = rule;
      this.mediator = mediator;
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
    * Returns the {@link KeYMediator} to use.
    * @return The {@link KeYMediator} to use.
    */
   public KeYMediator getMediator() {
      return mediator;
   }
   
   /**
    * Returns the {@link PosInSequent} to apply {@link BuiltInRule} on.
    * @return The {@link PosInSequent} to apply {@link BuiltInRule} on.
    */
   public PosInSequent getPosInSequent() {
      return pos;
   }
}