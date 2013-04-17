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

package de.hentschel.visualdbc.dbcmodel.diagram.part;

import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.emf.common.util.URI;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.osgi.util.NLS;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.dialogs.WizardNewFileCreationPage;

/**
 * @generated
 */
public class DbCCreationWizardPage extends WizardNewFileCreationPage {

   /**
    * @generated
    */
   private final String fileExtension;

   /**
    * @generated
    */
   public DbCCreationWizardPage(String pageName,
         IStructuredSelection selection, String fileExtension) {
      super(pageName, selection);
      this.fileExtension = fileExtension;
   }

   /**
    * Override to create files with this extension.
    * 
    * @generated
    */
   protected String getExtension() {
      return fileExtension;
   }

   /**
    * @generated
    */
   public URI getURI() {
      return URI.createPlatformResourceURI(getFilePath().toString(), false);
   }

   /**
    * @generated
    */
   protected IPath getFilePath() {
      IPath path = getContainerFullPath();
      if (path == null) {
         path = new Path(""); //$NON-NLS-1$
      }
      String fileName = getFileName();
      if (fileName != null) {
         path = path.append(fileName);
      }
      return path;
   }

   /**
    * @generated
    */
   public void createControl(Composite parent) {
      super.createControl(parent);
      setFileName(DbCDiagramEditorUtil.getUniqueFileName(
            getContainerFullPath(), getFileName(), getExtension()));
      setPageComplete(validatePage());
   }

   /**
    * @generated
    */
   protected boolean validatePage() {
      if (!super.validatePage()) {
         return false;
      }
      String extension = getExtension();
      if (extension != null
            && !getFilePath().toString().endsWith("." + extension)) {
         setErrorMessage(NLS.bind(Messages.DbCCreationWizardPageExtensionError,
               extension));
         return false;
      }
      return true;
   }
}