/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
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
   // TODO: Document missing members of class TacletCommandContributionItem

   private TacletApp app;
   
   private KeYMediator mediator;
   
   private PosInSequent pos;
   
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
   
   public TacletApp getTacletApp(){
      return app;
   }
   
   public KeYMediator getMediator(){
      return mediator;
   }
   
   public PosInSequent getPosInSequent(){
      return pos;
   }
}