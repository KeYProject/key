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
import de.uka.ilkd.key.rule.TacletApp;


/**
 * A customized {@link CommandContributionItem} which contains a {@link TacletApp}, a {@link KeYMediator} and a {@link PosInSequent}.
 * 
 * @author Christoph Schneider, Niklas Bunzel, Stefan Käsdorf, Marco Drebing
 */
public class TacletCommandContributionItem extends CommandContributionItem {
   /***
    * The {@link TacletApp} to apply.
    */
   private final TacletApp app;
   
   /**
    * The {@link KeYMediator} to use.
    */
   private final KeYMediator mediator;
   
   /**
    * The {@link PosInSequent} to apply {@link TacletApp} on.
    */
   private final PosInSequent pos;
   
   /**
    * The constructor with the additional parameters.
    * @param contributionParameters - the {@link CommandContributionItemParameter}.
    * @param app - the {@link TacletApp}.
    * @param mediator - the {@link KeYMediator}.
    * @param pos - the {@link PosInSequent}.
    */
   public TacletCommandContributionItem(CommandContributionItemParameter contributionParameters, TacletApp app, KeYMediator mediator, PosInSequent pos) {
      super(contributionParameters);
      this.app = app;
      this.mediator = mediator;
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
    * Returns the {@link KeYMediator} to use.
    * @return The {@link KeYMediator} to use.
    */
   public KeYMediator getMediator() {
      return mediator;
   }
   
   /**
    * Returns the {@link PosInSequent} to apply {@link TacletApp} on.
    * @return The {@link PosInSequent} to apply {@link TacletApp} on.
    */
   public PosInSequent getPosInSequent() {
      return pos;
   }
}