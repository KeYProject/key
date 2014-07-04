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

package org.key_project.key4eclipse.common.ui.wizard.page;

import java.io.File;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.jface.viewers.ArrayContentProvider;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.ListViewer;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Text;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.gui.ExampleChooser;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.gui.ExampleChooser.ShortFile;

/**
 * This {@link WizardPage} allows to select a KeY example.
 * @author Martin Hentschel
 */
public class KeYExampleWizardPage extends WizardPage {
   /**
    * Shows the available examples.
    */
   private ListViewer examplesViewer;
   
   /**
    * Shows the description of the selected example.
    */
   private Text descriptionText;
   
   /**
    * Maps an example to its description.
    */
   private Map<ShortFile, String> example2descriptionMap = new HashMap<ShortFile, String>();
   
   /**
    * Constructor.
    * @param pageName The name of this page.
    */
   public KeYExampleWizardPage(String pageName) {
      super(pageName);
      setTitle("KeY Examples");
      setDescription("Select one example to create a Java Project for.");
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void createControl(Composite parent) {
      Composite root = new Composite(parent, SWT.NONE);
      root.setLayout(new GridLayout(2, false));
      // Examples
      Group examplesGroup = new Group(root, SWT.NONE);
      examplesGroup.setLayoutData(new GridData(GridData.FILL_VERTICAL));
      examplesGroup.setText("Examples");
      examplesGroup.setLayout(new FillLayout());
      examplesViewer = new ListViewer(examplesGroup, SWT.BORDER | SWT.SINGLE);
      examplesViewer.addSelectionChangedListener(new ISelectionChangedListener() {
         @Override
         public void selectionChanged(SelectionChangedEvent event) {
            updatePageCompletedAndShownDescription();
         }
      });
      examplesViewer.setContentProvider(ArrayContentProvider.getInstance());
      File examplesDir = new File(Main.getExamplesDir());
      List<ShortFile> examples = ExampleChooser.listExamples(examplesDir);
      examplesViewer.setInput(examples);
      if (!examples.isEmpty()) {
         examplesViewer.setSelection(SWTUtil.createSelection(examples.get(0)));
      }
      // Description
      Group descriptionGroup = new Group(root, SWT.NONE);
      GridData descriptionGroupData = new GridData(GridData.FILL_BOTH);
      descriptionGroupData.widthHint = 400;
      descriptionGroup.setLayoutData(descriptionGroupData);
      descriptionGroup.setText("Description");
      descriptionGroup.setLayout(new FillLayout());
      descriptionText = new Text(descriptionGroup, SWT.BORDER | SWT.V_SCROLL | SWT.MULTI | SWT.WRAP);
      descriptionText.setEditable(false);
      setControl(root);
      updatePageCompletedAndShownDescription();
   }
   
   /**
    * Updates the page completed stated and the shown description when
    * the selected example has changed.
    */
   protected void updatePageCompletedAndShownDescription() {
      ShortFile selectedExample = getSelectedExample();
      if (selectedExample != null) {
         // Update page completed state
         setPageComplete(true);
         // Update shown description
         String description = example2descriptionMap.get(selectedExample);
         if (description == null) {
            description = ExampleChooser.readDescription(selectedExample);
            example2descriptionMap.put(selectedExample, description);
         }
         SWTUtil.setText(descriptionText, description);
      }
      else {
         // Update page completed state
         setPageComplete(false);
         // Update shown description
         descriptionText.setText(StringUtil.EMPTY_STRING);
      }
   }
   
   /**
    * Returns the selected example.
    * @return The selected example.
    */
   public ShortFile getSelectedExample() {
      Object selected = SWTUtil.getFirstElement(examplesViewer.getSelection());
      if (selected instanceof ShortFile) {
         return (ShortFile)selected;
      }
      else {
         return null;
      }
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * Changed visibility to public.
    * </p>
    */
   @Override
   public boolean isCurrentPage() {
      return super.isCurrentPage();
   };
}