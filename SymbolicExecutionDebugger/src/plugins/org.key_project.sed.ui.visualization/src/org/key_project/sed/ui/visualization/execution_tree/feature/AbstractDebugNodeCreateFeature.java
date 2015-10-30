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

package org.key_project.sed.ui.visualization.execution_tree.feature;

import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.DebugException;
import org.eclipse.graphiti.dt.IDiagramTypeProvider;
import org.eclipse.graphiti.features.ICreateFeature;
import org.eclipse.graphiti.features.ICustomUndoableFeature;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.context.IContext;
import org.eclipse.graphiti.features.context.ICreateContext;
import org.eclipse.graphiti.features.impl.AbstractCreateFeature;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.model.ISEThread;
import org.key_project.sed.core.model.memory.ISEMemoryNode;
import org.key_project.sed.core.model.memory.ISEMemoryDebugTarget;
import org.key_project.sed.ui.visualization.execution_tree.provider.ExecutionTreeDiagramTypeProvider;
import org.key_project.sed.ui.visualization.execution_tree.wizard.CreateDebugNodeWizard;
import org.key_project.sed.ui.visualization.execution_tree.wizard.CreateDebugNodeWizard.CreateDebugNodeWizardResult;
import org.key_project.sed.ui.visualization.util.LogUtil;
import org.key_project.util.eclipse.WorkbenchUtil;

/**
 * Provides a basic implementation of {@link ICreateFeature} for {@link ISENode}s.
 * @author Martin Hentschel
 */
public abstract class AbstractDebugNodeCreateFeature extends AbstractCreateFeature implements ICustomUndoableFeature {
   /**
    * The created {@link ISENode}.
    */
   private ISENode createdNode;
   
   /**
    * The index on {@link ISENode#getParent()} where the created node ({@link #createdNode}) was added to.
    */
   private int indexOnParent;
   
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link ICreateFeature}.
    */
   public AbstractDebugNodeCreateFeature(IFeatureProvider fp, String name, String description) {
      super(fp, name, description);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canCreate(ICreateContext context) {
      return context.getTargetContainer() instanceof Diagram;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Object[] create(ICreateContext context) {
      try {
         // Ask user for initial values
         CreateDebugNodeWizardResult result = CreateDebugNodeWizard.openWizard(WorkbenchUtil.getActiveShell(), 
                                                                               getNodeType(),
                                                                               getAvailableDebugTargets(),
                                                                               isThreadCreation(),
                                                                               getFeatureProvider()); 
         if (result != null) {
            // Create new business object
            ISEDebugTarget target = result.getTarget();
            ISENode parent = result.getParent();
            createdNode = createNewDebugNode(target, parent, result.getThread(), result.getName());
            if (isThreadCreation()) {
               Assert.isTrue(target instanceof ISEMemoryDebugTarget);
               Assert.isTrue(createdNode instanceof ISEThread);
               ((ISEMemoryDebugTarget)target).addSymbolicThread((ISEThread)createdNode);
            }
            else {
               Assert.isTrue(parent instanceof ISEMemoryNode);
               ((ISEMemoryNode)parent).addChild(createdNode);
            }
            // Do the add
            addGraphicalRepresentation(context, createdNode);
            // Return newly created business object(s)
            return new Object[] {createdNode};
         }
         else {
            return EMPTY;
         }
      }
      catch (DebugException e) {
         LogUtil.getLogger().logError(e);
         return EMPTY;
      }
   }
   
   /**
    * Returns the available {@link ISEDebugTarget}s.
    * @return The available {@link ISEDebugTarget}s.
    */
   protected ISEDebugTarget[] getAvailableDebugTargets()  {
      IDiagramTypeProvider dtp = getFeatureProvider().getDiagramTypeProvider();
      Assert.isTrue(dtp instanceof ExecutionTreeDiagramTypeProvider);
      ExecutionTreeDiagramTypeProvider provider = (ExecutionTreeDiagramTypeProvider)dtp;
      provider.makeSureThatDebugTargetIsAvailable();
      return provider.getDebugTargets();
   }
   
   /**
    * Defines if {@link ISEThread}s or other {@link ISENode}s should be created.
    * @return {@code true} create {@link ISEThread}s, {@code false} create other {@link ISENode}s.
    */
   protected boolean isThreadCreation() {
      return false;
   }
   
   /**
    * Returns the name of the node type that is created via this {@link ICreateFeature}.
    * @return The node type name.
    */
   protected abstract String getNodeType();

   /**
    * Creates a new {@link ISENode} to use as business object.
    * @param initialValues The initial values to use.
    * @return The created {@link ISENode}.
    * @throws DebugException Occurred Exception.
    */
   protected abstract ISENode createNewDebugNode(ISEDebugTarget target,
                                                       ISENode parent,
                                                       ISEThread thread,
                                                       String name) throws DebugException;

   /**
    * {@inheritDoc}
    */
   @Override
   public void undo(IContext context) {
      try {
         if (isThreadCreation()) {
            if (createdNode.getDebugTarget() instanceof ISEMemoryDebugTarget) {
               ISEMemoryDebugTarget target = (ISEMemoryDebugTarget)createdNode.getDebugTarget();
               indexOnParent = target.indexOfSymbolicThread((ISEThread)createdNode);
               target.removeSymbolicThread((ISEThread)createdNode);
            }
         }
         else {
            if (createdNode.getParent() instanceof ISEMemoryNode) {
               ISEMemoryNode parent = (ISEMemoryNode)createdNode.getParent();
               indexOnParent = parent.indexOfChild(createdNode);
               parent.removeChild(createdNode);
            }
         }
      }
      catch (DebugException e) {
         LogUtil.getLogger().logError(e);
         throw new RuntimeException(e);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canRedo(IContext context) {
      return true;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void redo(IContext context) {
      try {
         if (isThreadCreation()) {
            if (createdNode.getDebugTarget() instanceof ISEMemoryDebugTarget) {
               ISEMemoryDebugTarget target = (ISEMemoryDebugTarget)createdNode.getDebugTarget();
               target.addSymbolicThread(indexOnParent, (ISEThread)createdNode);
            }
         }
         else {
            if (createdNode.getParent() instanceof ISEMemoryNode) {
               ISEMemoryNode parent = (ISEMemoryNode)createdNode.getParent();
               parent.addChild(indexOnParent, createdNode);
            }
         }
      }
      catch (DebugException e) {
         LogUtil.getLogger().logError(e);
         throw new RuntimeException(e);
      }
   }
}