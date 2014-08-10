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

import org.eclipse.swt.SWT;
import org.eclipse.ui.menus.CommandContributionItem;
import org.eclipse.ui.menus.CommandContributionItemParameter;
import org.eclipse.ui.menus.ExtensionContributionFactory;
import org.eclipse.ui.menus.IContributionRoot;
import org.eclipse.ui.services.IServiceLocator;

public class RuleMenuExtensionContributionFactory extends
      ExtensionContributionFactory {

   public RuleMenuExtensionContributionFactory() {
      super();
   }

   @Override
   public void createContributionItems(IServiceLocator serviceLocator,
         IContributionRoot additions) {
      CommandContributionItemParameter p = new CommandContributionItemParameter(serviceLocator, null, "org.key_project.keyide.ui.commands.startAutoModeCommand", SWT.PUSH);
      p.label="Start Proof";
      
      CommandContributionItem item = new CommandContributionItem(p);
      item.setVisible(true);
      additions.addContributionItem(item, null);
   }

}