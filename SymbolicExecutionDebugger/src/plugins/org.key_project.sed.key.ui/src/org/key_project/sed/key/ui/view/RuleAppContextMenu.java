package org.key_project.sed.key.ui.view;

import java.util.Iterator;

import org.eclipse.swt.SWT;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.menus.CommandContributionItemParameter;
import org.eclipse.ui.menus.ExtensionContributionFactory;
import org.eclipse.ui.menus.IContributionRoot;
import org.eclipse.ui.services.IServiceLocator;
import org.key_project.keyide.ui.editor.BuiltInRuleCommandContributionItem;
import org.key_project.keyide.ui.editor.TacletCommandContributionItem;
import org.key_project.keyide.ui.util.KeYIDEUtil;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.eclipse.WorkbenchUtil;

import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * provides the context menu entries for manual rule application on {@link ManualView}.
 * @author Seena Vellaramkalayil
 *
 */
public class RuleAppContextMenu extends ExtensionContributionFactory {

   @Override
   public void createContributionItems(IServiceLocator serviceLocator,
         IContributionRoot additions) {
      IWorkbenchPart activeView = WorkbenchUtil.getActivePart();
      if (activeView instanceof ManualView) {
         ManualView view = (ManualView) activeView;
         Node node = view.getSelectedNode();
         Goal goal = view.getProof().getGoal(node);
         if (goal != null) {
            PosInSequent position = view.getSelectedPosInSequent();
            ImmutableList<TacletApp> appList = KeYIDEUtil.findTaclets(view.getEnvironment().getUi(),
                                                                      goal, position);
            if (appList != null) {
               Iterator<TacletApp> it = appList.iterator();
               while (it.hasNext()) {
                  TacletApp app = it.next();
                  CommandContributionItemParameter p = new CommandContributionItemParameter(serviceLocator, "", 
                                                                                            "org.key_project.sed.key.ui.commands.applyRule", 
                                                                                            SWT.PUSH);
                  p.label = app.rule().displayName();
                  TacletCommandContributionItem item = new TacletCommandContributionItem(p, goal, app, view.getEnvironment().getUi(), position);
                  item.setVisible(true);
                  additions.addContributionItem(item, null);
               }
            }
            ImmutableList<BuiltInRule> builtInRules = KeYIDEUtil.findBuiltInRules(view.getEnvironment().getUi(), goal, position);
            for (BuiltInRule rule: builtInRules) {
               CommandContributionItemParameter p = new CommandContributionItemParameter(serviceLocator, "", 
                                                                                         "org.key_project.sed.key.ui.commands.applyRule", 
                                                                                         SWT.PUSH);
               p.label = rule.displayName();
               BuiltInRuleCommandContributionItem item = new BuiltInRuleCommandContributionItem(p, goal, rule, view.getEnvironment().getUi(), position);
               item.setVisible(true);
               additions.addContributionItem(item,  null);
            }
            view.setManualRule(true);
         }
      }
   }

}
