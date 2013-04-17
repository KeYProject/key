package org.key_project.keyide.ui.editor;

import java.util.Iterator;

import org.eclipse.swt.SWT;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.menus.CommandContributionItemParameter;
import org.eclipse.ui.menus.ExtensionContributionFactory;
import org.eclipse.ui.menus.IContributionRoot;
import org.eclipse.ui.services.IServiceLocator;
import org.key_project.util.eclipse.WorkbenchUtil;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

/**
 * A ContextMenu for the applicable {@link TacletApp}s of the selected Term.
 * 
 * @author Christoph Schneider, Niklas Bunzel, Stefan K�sdorf, Marco Drebing
 */
public class TacletContextMenu extends ExtensionContributionFactory {
   /**
    * Creates a ContextMenu for all applicable {@link TacletApp}s by creating and adding {@link TacletCommandContributionItem}s to a {@link IContributionRoot}.
    * @param serviceLocator The given {@link IServiceLocator}.
    * @param additions The {@link IContributionRoot} the {@link TacletApp}s will be added.
    */
   @Override
   public void createContributionItems(IServiceLocator serviceLocator, IContributionRoot additions) {
      IEditorPart activeEditor = WorkbenchUtil.getActiveEditor();
      if (activeEditor instanceof KeYEditor) {
         KeYEditor keyEditor = (KeYEditor)activeEditor;
         KeYEnvironment<CustomConsoleUserInterface> environment = keyEditor.getKeYEnvironment();
         KeYMediator mediator = environment.getMediator();
         if(mediator.getSelectedNode().getAppliedRuleApp() == null){
            ProofSourceViewerDecorator textViewer = keyEditor.getTextViewer();
            PosInSequent pos = textViewer.getPosInSequent();
            ImmutableList<TacletApp> appList = textViewer.findRules(mediator, pos);
            // TODO: What about build in rules, are they not supported?
            if(appList != null){
               Iterator<TacletApp> it = appList.iterator();
               while(it.hasNext()){
                  TacletApp app = it.next();
                  CommandContributionItemParameter p = new CommandContributionItemParameter(serviceLocator, "", "org.key_project.keyide.ui.commands.applyrule", SWT.PUSH);
                  p.label = app.rule().displayName();
                  TacletCommandContributionItem item = new TacletCommandContributionItem(p, app, mediator, pos);
                  item.setVisible(true);
                  additions.addContributionItem(item, null);
               }
            }
         }
      }
   }
}