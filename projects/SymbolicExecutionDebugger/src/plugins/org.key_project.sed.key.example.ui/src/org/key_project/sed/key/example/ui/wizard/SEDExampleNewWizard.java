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

package org.key_project.sed.key.example.ui.wizard;

import java.util.Collections;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.jdt.internal.ui.wizards.NewWizardMessages;
import org.eclipse.jdt.ui.wizards.NewJavaProjectWizardPageOne;
import org.eclipse.jface.wizard.IWizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.key_project.key4eclipse.common.ui.wizard.AbstractNewJavaProjectWizard;
import org.key_project.key4eclipse.starter.core.property.KeYClassPathEntry;
import org.key_project.key4eclipse.starter.core.property.KeYClassPathEntry.KeYClassPathEntryKind;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.sed.key.example.ui.Activator;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.swt.SWTUtil;

/**
 * The "SED Examples" wizard used to create new Java Projects with examples
 * for the Symbolic Execution Debugger (SED).
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class SEDExampleNewWizard extends AbstractNewJavaProjectWizard {
   /**
    * {@inheritDoc}
    */
   @Override
   protected String getExampleName() {
      return "SED Examples";
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void addPages() {
      super.addPages();
      // Set initial project name.
      for (IWizardPage page : getPages()) {
         if (page instanceof NewJavaProjectWizardPageOne) {
            NewJavaProjectWizardPageOne one = (NewJavaProjectWizardPageOne)page;
            one.setProjectName(getExampleName());
         }
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IWizardPage getNextPage(IWizardPage page) {
      // Make sure that only the first wizard page is available.
      IWizardPage nextPage = super.getNextPage(page);
      if (nextPage instanceof NewJavaProjectWizardPageOne) {
         return nextPage;
      }
      else {
         return null;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void createPageControls(Composite pageContainer) {
      super.createPageControls(pageContainer);
      // Make sure that separate folders are used
      for (IWizardPage page : getPages()) {
         if (page instanceof NewJavaProjectWizardPageOne) {
            NewJavaProjectWizardPageOne one = (NewJavaProjectWizardPageOne)page;
            Button oneFolderButton = SWTUtil.findButtonByText(one.getControl(), NewWizardMessages.NewJavaProjectWizardPageOne_LayoutGroup_option_oneFolder);
            oneFolderButton.setSelection(false);
            oneFolderButton.notifyListeners(SWT.Selection, null);
            oneFolderButton.setEnabled(false);
            Button separateFoldersButton = SWTUtil.findButtonByText(one.getControl(), NewWizardMessages.NewJavaProjectWizardPageOne_LayoutGroup_option_separateFolders);
            separateFoldersButton.setSelection(true);
            separateFoldersButton.notifyListeners(SWT.Selection, null);
            separateFoldersButton.setEnabled(false);
         }
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean createExampleContent(IContainer sourceDirectory) throws Exception {
      // Add specs folder
      IProject project = sourceDirectory.getProject();
      IFolder libSpecsFolder = project.getFolder("lib_specs");
      if (!libSpecsFolder.exists()) {
         libSpecsFolder.create(true, true, null);
      }
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/lib_specs", libSpecsFolder);
      KeYResourceProperties.setClassPathEntries(project, Collections.singletonList(new KeYClassPathEntry(KeYClassPathEntryKind.WORKSPACE, libSpecsFolder.getFullPath().toString())));
      // Add examples to src folder
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/src", sourceDirectory);
      // Add readme file
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/Readme.txt", project);
      // Open readme
      IResource firstExample = project.findMember("Readme.txt");
      if (firstExample instanceof IFile) {
         selectAndReveal(firstExample);
         openResource((IFile)firstExample);
      }
      return true;
   }
}