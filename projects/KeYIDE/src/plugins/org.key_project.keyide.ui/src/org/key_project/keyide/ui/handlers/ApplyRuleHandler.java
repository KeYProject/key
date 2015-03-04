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

package org.key_project.keyide.ui.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.swt.widgets.Event;
import org.key_project.keyide.ui.editor.BuiltInRuleCommandContributionItem;
import org.key_project.keyide.ui.editor.TacletCommandContributionItem;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.rule.BuiltInRule;
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
      Object trigger = event.getTrigger();
      if (trigger instanceof Event) {
         Event swtEvent = (Event)trigger;
         Object data = swtEvent.widget.getData();
         if (data instanceof TacletCommandContributionItem) {
            TacletCommandContributionItem item = (TacletCommandContributionItem)data;
            TacletApp app = item.getTacletApp();
            UserInterfaceControl ui = item.getUi();
            PosInSequent pos = item.getPosInSequent();
            if (!ui.getProofControl().selectedTaclet(app.taclet(), item.getGoal(), pos.getPosInOccurrence())) {
               throw new IllegalStateException("Taclet application failed." + app.rule().name());
            }
         }
         else if (data instanceof BuiltInRuleCommandContributionItem) {
            BuiltInRuleCommandContributionItem item = (BuiltInRuleCommandContributionItem)data;
            BuiltInRule rule = item.getRule();
            UserInterfaceControl ui = item.getUi();
            PosInSequent pos = item.getPosInSequent();
            ui.getProofControl().selectedBuiltInRule(item.getGoal(), rule, pos.getPosInOccurrence(), false);
         }
      }
      return null;
   }
}