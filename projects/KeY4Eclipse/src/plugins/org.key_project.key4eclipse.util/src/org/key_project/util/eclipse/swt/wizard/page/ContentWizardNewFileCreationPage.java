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

package org.key_project.util.eclipse.swt.wizard.page;

import java.io.InputStream;

import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.dialogs.WizardNewFileCreationPage;

/**
 * Extends the functionality of {@link WizardNewFileCreationPage}:
 * <ul>
 *    <li>
 *       Allows to set the initial content of new created files ({@link #createNewFile()}) via {@link #setInitialContents(InputStream)}. 
 *       <b>Attention:</b> If in the advanced option a local file is defined it is not changed or created with empty content.
 *    </li>
 *    <li>Allows to check if the current page is shown in the wizard via {@link #isCurrentPage()}.</li>
 * </ul>
 * @author Martin Hentschel
 */
public class ContentWizardNewFileCreationPage extends WizardNewFileCreationPage {
   /**
    * The content to set in new created files.
    */
   private InputStream initialContents;

   /**
    * Creates a new file creation wizard page. If the initial resource
    * selection contains exactly one container resource then it will be used as
    * the default container resource.
    * @param pageName The name of the page
    * @param selection The current resource selection
    */
   public ContentWizardNewFileCreationPage(String pageName, IStructuredSelection selection) {
      super(pageName, selection);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public InputStream getInitialContents() {
      return initialContents;
   }

   /**
    * Sets the initial content of new created files.
    * @param initialContents The new content.
    */
   public void setInitialContents(InputStream initialContents) {
      this.initialContents = initialContents;
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * Changed visibiltity to public.
    * </p>
    */
   @Override
   public boolean isCurrentPage() {
      return super.isCurrentPage();
   }
}