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

import java.util.Iterator;

import org.eclipse.swt.SWT;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.menus.CommandContributionItemParameter;
import org.eclipse.ui.menus.ExtensionContributionFactory;
import org.eclipse.ui.menus.IContributionRoot;
import org.eclipse.ui.services.IServiceLocator;
import org.key_project.keyide.ui.util.KeYIDEUtil;
import org.key_project.util.eclipse.WorkbenchUtil;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * A ContextMenu for the applicable {@link TacletApp}s of the selected Term.
 * 
 * @author Christoph Schneider, Niklas Bunzel, Stefan Käsdorf, Marco Drebing
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
         KeYMediator mediator = keyEditor.getMediator();
         if (mediator != null && mediator.getSelectedNode().getAppliedRuleApp() == null) {
            PosInSequent pos = keyEditor.getSelectedPosInSequent();
            ImmutableList<TacletApp> appList = KeYIDEUtil.findRules(mediator, pos);
            // TODO: What about build in rules, are they not supported?
            if (appList != null) {
               Iterator<TacletApp> it = appList.iterator();
               while (it.hasNext()) {
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