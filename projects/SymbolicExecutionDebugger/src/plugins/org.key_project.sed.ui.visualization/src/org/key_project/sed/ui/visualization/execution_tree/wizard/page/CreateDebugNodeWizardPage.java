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

package org.key_project.sed.ui.visualization.execution_tree.wizard.page;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.DebugException;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.key_project.sed.core.model.ISEDDebugElement;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.util.ISEDIterator;
import org.key_project.sed.core.util.SEDPreorderIterator;
import org.key_project.sed.ui.visualization.execution_tree.wizard.CreateDebugNodeWizard;
import org.key_project.sed.ui.visualization.util.LogUtil;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.java.StringUtil;

/**
 * {@link WizardPage} to define the initial values of new {@link ISEDDebugNode}s.
 * @author Martin Hentschel
 * @see CreateDebugNodeWizard
 */
public class CreateDebugNodeWizardPage extends WizardPage {
   /**
    * The existing {@link ISEDDebugTarget}s shown in {@link #targetCombo}.
    */
   private ISEDDebugTarget[] debugTargets;
   
   /**
    * Indicates that threads should be created.
    */
   private boolean threadCreation;
   
   /**
    * The used {@link IFeatureProvider}.
    */
   private IFeatureProvider featureProvider;
   
   /**
    * Input field for the name.
    */
   private Text nameText;
   
   /**
    * {@link Combo} to select {@link ISEDDebugTarget}s.
    */
   private Combo targetCombo;
   
   /**
    * {@link Combo} to select {@link ISEDThread}s.
    */
   private Combo threadCombo;
   
   /**
    * Input field to define the parent in the {@link ISEDThread}.
    */
   private Combo parentCombo;
   
   /**
    * The shown {@link ISEDThread}s in {@link #threadCombo}.
    */
   private ISEDThread[] threads;
   
   /**
    * The shown {@link ISEDDebugNode}s in {@link #parentCombo}.
    */
   private List<ISEDDebugNode> parents;
   
   /**
    * Constructor.
    * @param pageName The page name.
    * @param nodeType The name of the node type which should be created.
    * @param debugTargets The existing {@link ISEDDebugTarget}s.
    * @param threadCreation Indicates that threads should be created.
    * @param featureProvider The {@link IFeatureProvider} to use.
    */
   public CreateDebugNodeWizardPage(String pageName, 
                                    String nodeType, 
                                    ISEDDebugTarget[] debugTargets,
                                    boolean threadCreation,
                                    IFeatureProvider featureProvider) {
      super(pageName);
      Assert.isNotNull(debugTargets);
      Assert.isNotNull(featureProvider);
      this.debugTargets = debugTargets;
      this.threadCreation = threadCreation;
      this.featureProvider = featureProvider;
      setTitle("Create " + nodeType);
      setDescription("Define the properties for the new " + nodeType + ".");
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void createControl(Composite parent) {
      // Create root
      Composite root = new Composite(parent, SWT.NONE);
      root.setLayout(new GridLayout(2, false));
      setControl(root);
      // Create name 
      Label nameLabel = new Label(root, SWT.NONE);
      nameLabel.setText("&Name");
      nameText = new Text(root, SWT.BORDER);
      nameText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      nameText.addModifyListener(new ModifyListener() {
         @Override
         public void modifyText(ModifyEvent e) {
            updatePageCompleted();
         }
      });
      // Debug target
      if (isTargetComboShown()) {
         Label targetLabel = new Label(root, SWT.NONE);
         targetLabel.setText("&Debug Target");
         targetCombo = new Combo(root, SWT.READ_ONLY);
         targetCombo.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
         targetCombo.addSelectionListener(new SelectionAdapter() {
            @Override
            public void widgetSelected(SelectionEvent e) {
               updateThreads();
               updatePageCompleted();
            }
         });
         for (ISEDDebugTarget target : debugTargets) {
            SWTUtil.add(targetCombo, ObjectUtil.toString(target));
         }
      }
      if (!isThreadCreation()) {
         // Thread combo
         Label threadLabel = new Label(root, SWT.NONE);
         threadLabel.setText("&Thread");
         threadCombo = new Combo(root, SWT.READ_ONLY);
         threadCombo.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
         threadCombo.addSelectionListener(new SelectionAdapter() {
            @Override
            public void widgetSelected(SelectionEvent e) {
               updateParents();
               updatePageCompleted();
            }
         });
         // Parent combo
         Label parentLabel = new Label(root, SWT.NONE);
         parentLabel.setText("&Parent");
         parentCombo = new Combo(root, SWT.READ_ONLY);
         parentCombo.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
         parentCombo.addSelectionListener(new SelectionAdapter() {
            @Override
            public void widgetSelected(SelectionEvent e) {
               updatePageCompleted();
            }
         });
      }
      // Select default values
      if (isTargetComboShown()) {
         selectFirstItem(targetCombo);
      }
      updateThreads();
      // Update page completed
      updatePageCompleted();
   }

   /**
    * Updates the available {@link ISEDThread}s in {@link #threadCombo}.
    */
   protected void updateThreads() {
      try {
         if (!isThreadCreation()) {
            // Remove old items
            threadCombo.removeAll();
            // Add new items if possible
            ISEDDebugTarget target = getTarget();
            if (target != null) {
               threads = target.getSymbolicThreads();
               for (ISEDThread thread : threads) {
                  SWTUtil.add(threadCombo, ObjectUtil.toString(thread));
               }
               // Select first item
               selectFirstItem(threadCombo);
            }
            // Update parents
            updateParents();
         }
      }
      catch (DebugException e) {
         LogUtil.getLogger().logError(e);
         LogUtil.getLogger().openErrorDialog(getShell(), e);
      }
   }
   
   /**
    * Updates the available {@link ISEDDebugNode}s in {@link #parentCombo}.
    */   
   protected void updateParents() {
      try {
         if (!isThreadCreation()) {
            // Remove old items
            parentCombo.removeAll();
            // Add new items if possible
            ISEDThread thread = getThread();
            if (thread != null) {
               parents = listParents(thread);
               for (ISEDDebugNode parent : parents) {
                  SWTUtil.add(parentCombo, ObjectUtil.toString(parent));
               }
               // Select first item
               selectFirstItem(parentCombo);
            }
         }
      }
      catch (DebugException e) {
         LogUtil.getLogger().logError(e);
         LogUtil.getLogger().openErrorDialog(getShell(), e);
      }
   }
   
   /**
    * Collects the contained {@link ISEDDebugNode}s in the given {@link ISEDThread}.
    * @param thread The given {@link ISEDThread}.
    * @return The contained {@link ISEDDebugNode}s.
    * @throws DebugException Occurred Exception.
    */
   protected List<ISEDDebugNode> listParents(ISEDThread thread) throws DebugException {
      LinkedList<ISEDDebugNode> children = new LinkedList<ISEDDebugNode>();
      ISEDIterator iter = new SEDPreorderIterator(thread);
      while (iter.hasNext()) {
         ISEDDebugElement next = iter.next();
         if (next instanceof ISEDDebugNode) {
            PictogramElement pe = featureProvider.getPictogramElementForBusinessObject(next);
            if (pe != null) { // Do not include hidden (removed) elements
               children.addFirst((ISEDDebugNode)next);
            }
         }
      }
      return children;
   }

   /**
    * Selects the first item if possible in the given {@link Combo}.
    * @param combo The {@link Combo} to select the first item in.
    */
   protected void selectFirstItem(Combo combo) {
      if (combo.getItemCount() >= 1) {
         combo.setText(combo.getItem(0));
      }
   }

   /**
    * Updates the page completed status.
    */
   protected void updatePageCompleted() {
      // Compute page completed status
      boolean valid = !StringUtil.isTrimmedEmpty(getNameValue());
      if (!valid) {
         setErrorMessage("No name defined.");
      }
      if (valid) {
         valid = getTarget() != null;
         if (!valid) {
            setErrorMessage("No debug target selected.");
         }
      }
      if (valid && !isThreadCreation()) {
         valid = getThread() != null;
         if (!valid) {
            setErrorMessage("No thread selected.");
         }
      }
      if (valid && !isThreadCreation()) {
         valid = getParent() != null;
         if (!valid) {
            setErrorMessage("No parent selected.");
         }
      }
      // Update page completed status
      setPageComplete(valid);
      if (valid) {
         setErrorMessage(null);
      }
   }

   /**
    * Returns the defined name.
    * @return The defined name.
    */
   public String getNameValue() {
      return nameText.getText();
   }
   
   /**
    * Checks if {@link ISEDThread}s should be created.
    * @return {@code true} create threads, {@code false} create other {@link ISEDDebugNode}s.
    */
   public boolean isThreadCreation() {
      return threadCreation;
   }
   
   /**
    * Returns the selected {@link ISEDDebugTarget}.
    * @return The selected {@link ISEDDebugTarget}.
    */
   public ISEDDebugTarget getTarget() {
      if (isTargetComboShown()) {
         int index = targetCombo.getSelectionIndex();
         if (index >= 0 && index < debugTargets.length) {
            return debugTargets[index];
         }
         else {
            return null;
         }
      }
      else {
         return debugTargets[0];
      }
   }
   
   /**
    * Returns the selected parent {@link ISEDDebugNode}.
    * @return The parent {@link ISEDDebugNode}.
    */
   public ISEDDebugNode getParent() {
      if (!isThreadCreation()) {
         int index = parentCombo.getSelectionIndex();
         if (index >= 0 && index < parents.size()) {
            return parents.get(index);
         }
         else {
            return null;
         }
      }
      else {
         return null;
      }
   }
   
   /**
    * Returns the selected {@link ISEDThread}.
    * @return The selected {@link ISEDThread}.
    */
   public ISEDThread getThread() {
      if (!isThreadCreation()) {
         int index = threadCombo.getSelectionIndex();
         if (index >= 0 && index < threads.length) {
            return threads[index];
         }
         else {
            return null;
         }
      }
      else {
         return null;
      }
   }
   
   /**
    * Checks if the debug target combo {@link #targetCombo} is shown or not.
    * @return {@code true} is shown, {@code false} is not shown.
    */
   public boolean isTargetComboShown() {
      return debugTargets.length != 1;
   }
}