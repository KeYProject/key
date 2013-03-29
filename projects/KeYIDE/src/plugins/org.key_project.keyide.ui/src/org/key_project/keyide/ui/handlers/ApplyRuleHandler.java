package org.key_project.keyide.ui.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.swt.widgets.Event;
import org.eclipse.ui.handlers.HandlerUtil;
import org.eclipse.ui.internal.WorkbenchWindow;
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
