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

package org.key_project.sed.ui.visualization.execution_tree.wizard;

import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.widgets.Shell;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.model.ISEThread;
import org.key_project.sed.ui.visualization.execution_tree.wizard.page.CreateDebugNodeWizardPage;

/**
 * {@link Wizard} to define the initial values of new {@link ISENode}s.
 * @author Martin Hentschel
 * @see CreateDebugNodeWizardPage
 */
public class CreateDebugNodeWizard extends Wizard {
   /**
    * The contained {@link CreateDebugNodeWizardPage}.
    */
   private CreateDebugNodeWizardPage propertyPage;
   
   /**
    * The name of the node type which should be created.
    */
   private String nodeType;

   /**
    * The existing {@link ISEDebugTarget}s.
    */
   private ISEDebugTarget[] debugTargets;
   
   /**
    * Indicates that threads should be created.
    */
   private boolean threadCreation;
   
   /**
    * The used {@link IFeatureProvider}.
    */
   private IFeatureProvider featureProvider;

   /**
    * The result of this {@link Wizard}.
    */
   private CreateDebugNodeWizardResult result;
   
   /**
    * Constructor.
    * @param nodeType The name of the node type which should be created.
    * @param debugTargets The existing {@link ISEDebugTarget}s.
    * @param threadCreation Indicates that threads should be created.
    * @param featureProvider The {@link IFeatureProvider} to use.
    */
   public CreateDebugNodeWizard(String nodeType, 
                                ISEDebugTarget[] debugTargets,
                                boolean threadCreation,
                                IFeatureProvider featureProvider) {
      super();
      this.nodeType = nodeType;
      this.debugTargets = debugTargets;
      this.threadCreation = threadCreation;
      this.featureProvider = featureProvider;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void addPages() {
      setWindowTitle("Create " + nodeType);
      propertyPage = new CreateDebugNodeWizardPage("propertyPage", 
                                                   nodeType, 
                                                   debugTargets, 
                                                   threadCreation, 
                                                   featureProvider);
      addPage(propertyPage);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean performFinish() {
      result = new CreateDebugNodeWizardResult(propertyPage.getNameValue(),
                                               propertyPage.getTarget(),
                                               propertyPage.getParent(),
                                               propertyPage.getThread());
      return true;
   }
   
   /**
    * Returns the wizard result.
    * @return The wizard result or {@code null} if the wizard was canceled.
    */
   public CreateDebugNodeWizardResult getResult() {
      return result;
   }

   /**
    * Opens the this {@link Wizard} in an {@link WizardDialog}.
    * @param parentShell The parent {@link Shell} to use.
    * @param nodeType The name of the node type which should be created.
    * @param debugTargets The existing {@link ISEDebugTarget}s.
    * @param threadCreation Indicates that threads should be created.
    * @param featureProvider The {@link IFeatureProvider} to use.
    * @return The wizard result or {@code null} if the wizard was canceled.
    */
   public static CreateDebugNodeWizardResult openWizard(Shell parentShell, 
                                                        String nodeType, 
                                                        ISEDebugTarget[] debugTargets,
                                                        boolean threadCreation,
                                                        IFeatureProvider featureProvider) {
      CreateDebugNodeWizard wizard = new CreateDebugNodeWizard(nodeType, 
                                                               debugTargets, 
                                                               threadCreation, 
                                                               featureProvider);
      WizardDialog dialog = new WizardDialog(parentShell, wizard);
      dialog.setHelpAvailable(false);
      if (dialog.open() == WizardDialog.OK) {
         return wizard.getResult();
      }
      else {
         return null;
      }
   }
   
   /**
    * The wizard result with the defined settings.
    * @author Martin Hentschel
    */
   public static class CreateDebugNodeWizardResult {
      /**
       * The name of the {@link ISENode} to create.
       */
      private String name;
      
      /**
       * The selected {@link ISEDebugTarget}.
       */
      private ISEDebugTarget target;

      /**
       * The selected parent {@link ISENode} or {@code null} if an {@link ISEThread} should be created.
       */
      private ISENode parent;
      
      /**
       * The selected {@link ISEThread} or {@code null} if an {@link ISEThread} should be created.
       */
      private ISEThread thread;
      
      /**
       * Constructor.
       * @param name The name of the {@link ISENode} to create.
       * @param target The selected {@link ISEDebugTarget}.
       * @param parent The selected parent {@link ISENode} or {@code null} if an {@link ISEThread} should be created.
       * @param thread The selected {@link ISEThread} or {@code null} if an {@link ISEThread} should be created.
       */
      public CreateDebugNodeWizardResult(String name, 
                                         ISEDebugTarget target, 
                                         ISENode parent, 
                                         ISEThread thread) {
         super();
         this.name = name;
         this.target = target;
         this.parent = parent;
         this.thread = thread;
      }

      /**
       * Returns the name of the {@link ISENode} to create.
       * @return The name of the {@link ISENode} to create.
       */
      public String getName() {
         return name;
      }

      /**
       * Returns the selected {@link ISEDebugTarget}.
       * @return The selected {@link ISEDebugTarget}.
       */
      public ISEDebugTarget getTarget() {
         return target;
      }

      /**
       * Returns the selected parent {@link ISENode} or {@code null} if an {@link ISEThread} should be created.
       * @return The selected parent {@link ISENode} or {@code null} if an {@link ISEThread} should be created.
       */
      public ISENode getParent() {
         return parent;
      }

      /**
       * Returns the selected {@link ISEThread} or {@code null} if an {@link ISEThread} should be created.
       * @return The selected {@link ISEThread} or {@code null} if an {@link ISEThread} should be created.
       */
      public ISEThread getThread() {
         return thread;
      }
   }
}