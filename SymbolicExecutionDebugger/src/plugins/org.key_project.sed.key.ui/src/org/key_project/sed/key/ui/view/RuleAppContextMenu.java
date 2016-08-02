package org.key_project.sed.key.ui.view;

import java.util.HashMap;
import java.util.Iterator;

import org.eclipse.jface.action.MenuManager;
import org.eclipse.swt.SWT;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.menus.CommandContributionItemParameter;
import org.eclipse.ui.menus.ExtensionContributionFactory;
import org.eclipse.ui.menus.IContributionRoot;
import org.eclipse.ui.services.IServiceLocator;
import org.key_project.keyide.ui.editor.BuiltInRuleCommandContributionItem;
import org.key_project.keyide.ui.editor.MacroCommandContributionItem;
import org.key_project.keyide.ui.editor.TacletCommandContributionItem;
import org.key_project.keyide.ui.util.KeYIDEUtil;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.eclipse.WorkbenchUtil;

import de.uka.ilkd.key.gui.ProofMacroMenu;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * Provides the context menu entries in the sequent view as part of the {@link ProofView}.
 * @author Seena Vellaramkalayil
 */
public class RuleAppContextMenu extends ExtensionContributionFactory {
   /**
    * {@inheritDoc}
    */
   @Override
   public void createContributionItems(IServiceLocator serviceLocator, IContributionRoot additions) {
      IWorkbenchPart activeView = WorkbenchUtil.getActivePart();
      if (activeView instanceof ProofView) {
         ProofView view = (ProofView) activeView;
         Node node = view.getSelectedNode();
         if (node != null) {
            Goal goal = view.getCurrentProof().getGoal(node);
            if (goal != null) {
               PosInSequent position = view.getSelectedPosInSequent();
               // Add taclet apps
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
               // Add built in rules
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
               
               
               // Add macros
               MenuManager macroMenu = new MenuManager("Strategy macros");
               HashMap<String, MenuManager> subMenus = new HashMap<String, MenuManager>();
               Iterable<ProofMacro> allMacros = ProofMacroMenu.REGISTERED_MACROS;
               for (ProofMacro macro : allMacros) {
                  if (position != null) {
                       if (macro.canApplyTo(goal.node(), position.getPosInOccurrence())) {
                           CommandContributionItemParameter p = new CommandContributionItemParameter(serviceLocator, "", 
                                                                                            "org.key_project.sed.key.ui.commands.applyRule", SWT.PUSH);
                           p.label = macro.getName();
                           MacroCommandContributionItem item = new MacroCommandContributionItem(p, goal.node(), macro, view.getEnvironment().getUi(), position);
                           item.setVisible(true);
                           
                           // group macros into submenus depending on their category
                           String cat = macro.getCategory();
                           if (cat == null) {
                             macroMenu.add(item);
                           } else if (subMenus.containsKey(cat)) {
                             subMenus.get(cat).add(item);
                           } else {
                             MenuManager subMenu = new MenuManager(cat);
                             subMenu.add(item);
                             subMenus.put(cat, subMenu);
                           }  
                        }
                  }
               }
               // add submenus to the macro menu
               for (String category : subMenus.keySet())  {
                  macroMenu.add(subMenus.get(category));
               }
               additions.addContributionItem(macroMenu, null); 
            }
         }
      }
   }
}
