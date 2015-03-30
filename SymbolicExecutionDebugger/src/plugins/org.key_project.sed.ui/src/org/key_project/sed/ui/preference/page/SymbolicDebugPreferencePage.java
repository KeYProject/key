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

package org.key_project.sed.ui.preference.page;

import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

/**
 * Preference page for the Symbolic Execution Debugger (SED).
 * @author Martin Hentschel
 */
public class SymbolicDebugPreferencePage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage {
   /**
    * Constructor
    */
   public SymbolicDebugPreferencePage() {
      super(GRID);
      noDefaultAndApplyButton();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void init(IWorkbench workbench) {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void createFieldEditors() {
      // Maybe this page is filled in the future with real content, now it is only a category in the tree.
   }
}