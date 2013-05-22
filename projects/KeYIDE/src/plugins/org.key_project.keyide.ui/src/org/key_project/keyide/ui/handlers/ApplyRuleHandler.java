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

package org.key_project.keyide.ui.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.swt.widgets.Event;
import org.key_project.keyide.ui.editor.TacletCommandContributionItem;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * A {@link AbstractHandler} to handle the manual appliance of a {@link TacletApp}.
 * 
 * @author Christoph Schneider, Niklas Bunzel, Stefan Käsdorf, Marco Drebing
 */
public class ApplyRuleHandler extends AbstractHandler {
   /**
    * {@inheritDoc}
    */
   @Override
   public Object execute(ExecutionEvent event) throws ExecutionException {
      TacletCommandContributionItem item = (TacletCommandContributionItem)((Event)event.getTrigger()).widget.getData();
      TacletApp app = item.getTacletApp();
      KeYMediator mediator = item.getMediator();
      PosInSequent pos = item.getPosInSequent();
      mediator.selectedTaclet(app, pos);
      return null;
   }
}