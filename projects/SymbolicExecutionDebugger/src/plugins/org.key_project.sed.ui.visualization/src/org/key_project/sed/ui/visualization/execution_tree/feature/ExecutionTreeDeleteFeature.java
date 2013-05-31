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

package org.key_project.sed.ui.visualization.execution_tree.feature;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.DebugException;
import org.eclipse.graphiti.features.ICustomUndoableFeature;
import org.eclipse.graphiti.features.IDeleteFeature;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.context.IContext;
import org.eclipse.graphiti.features.context.IDeleteContext;
import org.eclipse.graphiti.features.context.impl.DeleteContext;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.ui.features.DefaultDeleteFeature;
import org.key_project.sed.core.model.ISEDDebugElement;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.model.memory.ISEDMemoryDebugNode;
import org.key_project.sed.core.model.memory.ISEDMemoryDebugTarget;
import org.key_project.sed.core.util.ISEDIterator;
import org.key_project.sed.core.util.SEDPreorderIterator;
import org.key_project.sed.ui.visualization.execution_tree.provider.ExecutionTreeFeatureProvider;
import org.key_project.sed.ui.visualization.util.EditableMultiDeleteInfo;

/**
 * <p>
 * Implementation of {@link IDeleteFeature} for {@link ISEDDebugNode}s
 * to make sure that the complete subtree of the selected {@link ISEDDebugNode}
 * is deleted and removed from the diagram.
 * </p>
 * <p> 
 * This feature is the only one which is used in the wohle execution tree diagram.
 * It means that {@link ExecutionTreeFeatureProvider#getDeleteFeature(IDeleteContext)}
 * always returns an instance of this class.
 * </p>
 * @author Martin Hentschel
 */
public class ExecutionTreeDeleteFeature extends DefaultDeleteFeature implements ICustomUndoableFeature {
   /**
    * Contains information for undo/redo provided by this {@link ICustomUndoableFeature}.
    */
   private List<DeleteUndoRedoContext> undoRedoContexts = new LinkedList<DeleteUndoRedoContext>();

   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} to use.
    */
   public ExecutionTreeDeleteFeature(IFeatureProvider fp) {
      super(fp);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canDelete(IDeleteContext context) {
      return super.canDelete(context) && 
             getFeatureProvider().getBusinessObjectForPictogramElement(context.getPictogramElement()) != null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void execute(IContext context) {
      try {
         if (context instanceof IDeleteContext) {
            // Instantiate DeleteContext for each element in the sub tree
            List<DeleteContext> children = new LinkedList<DeleteContext>();
            PictogramElement pe = ((IDeleteContext)context).getPictogramElement();
            Object[] businessObjectsForPictogramElement = getAllBusinessObjectsForPictogramElement(pe);
            EditableMultiDeleteInfo multiDeleteInfo = new EditableMultiDeleteInfo(true, false);
            for (Object businessObject : businessObjectsForPictogramElement) {
               if (businessObject instanceof ISEDDebugElement) {
                  ISEDIterator iter = new SEDPreorderIterator((ISEDDebugElement)businessObject);
                  while (iter.hasNext()) {
                     ISEDDebugElement next = iter.next();
                     PictogramElement childPe = getFeatureProvider().getPictogramElementForBusinessObject(next);
                     if (childPe != null) {
                        DeleteContext childContext = new DeleteContext(childPe);
                        childContext.setMultiDeleteInfo(multiDeleteInfo);
                        children.add(childContext);
                     }                  
                  }
               }
            }
            // Delete the whole sub tree defined by the starting element in the given IContext
            if (children.size() == 1) {
               DeleteContext childContext = children.get(0);
               childContext.setMultiDeleteInfo(null);
               delete(childContext);
            }
            else {
               multiDeleteInfo.setNumber(children.size());
               for (IDeleteContext child : children) {
                  delete(child);
               }
            }
         }
      }
      catch (DebugException e) {
         throw new RuntimeException(e);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void preDelete(IDeleteContext context) {
      super.preDelete(context);
      // Delete the whole sub tree in the business model.
      PictogramElement pe = ((IDeleteContext)context).getPictogramElement();
      Object[] businessObjectsForPictogramElement = getAllBusinessObjectsForPictogramElement(pe);
      for (Object businessObject : businessObjectsForPictogramElement) {
         if (businessObject instanceof ISEDDebugNode) {
            ISEDDebugNode node = (ISEDDebugNode)businessObject;
            DeleteUndoRedoContext undoRedoContext = new DeleteUndoRedoContext(node);
            removeFromParent(undoRedoContext);
            undoRedoContexts.add(undoRedoContext);
         }
      }
   }
   
   /**
    * Deletes the {@link ISEDDebugNode} defined by the given
    * {@link DeleteUndoRedoContext} in the business model.
    * @param context The {@link DeleteUndoRedoContext} to work with.
    */
   protected void removeFromParent(DeleteUndoRedoContext context) {
      try {
         ISEDDebugNode node = context.getNode();
         if (node instanceof ISEDThread) {
            ISEDThread thread = (ISEDThread)node;
            ISEDDebugTarget target = thread.getDebugTarget();
            Assert.isTrue(target instanceof ISEDMemoryDebugTarget);
            ISEDMemoryDebugTarget debugTarget = (ISEDMemoryDebugTarget)target;
            int index = debugTarget.indexOfSymbolicThread(thread);
            context.setIndexOnParent(index);
            debugTarget.removeSymbolicThread(thread);
         }
         else {
            ISEDDebugNode parent = node.getParent();
            Assert.isTrue(parent instanceof ISEDMemoryDebugNode);
            ISEDMemoryDebugNode parentNode = (ISEDMemoryDebugNode)parent;
            int index = parentNode.indexOfChild(node);
            context.setIndexOnParent(index);
            parentNode.removeChild(node);
         }
      }
      catch (DebugException e) {
         throw new RuntimeException(e);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void undo(IContext context) {
      // Restore the whole sub tree in the business model.
      for (DeleteUndoRedoContext undoRedoContext : undoRedoContexts) {
         addToParent(undoRedoContext);
      }
   }
   
   /**
    * Adds the node defined by the given {@link DeleteUndoRedoContext}
    * back to the business model.
    * @param context The {@link DeleteUndoRedoContext} to work with.
    */
   protected void addToParent(DeleteUndoRedoContext context) {
      try {
         ISEDDebugNode node = context.getNode();
         if (node instanceof ISEDThread) {
            ISEDThread thread = (ISEDThread)node;
            ISEDDebugTarget target = thread.getDebugTarget();
            Assert.isTrue(target instanceof ISEDMemoryDebugTarget);
            ISEDMemoryDebugTarget debugTarget = (ISEDMemoryDebugTarget)target;
            debugTarget.addSymbolicThread(context.getIndexOnParent(), thread);
         }
         else {
            ISEDDebugNode parent = node.getParent();
            Assert.isTrue(parent instanceof ISEDMemoryDebugNode);
            ISEDMemoryDebugNode parentNode = (ISEDMemoryDebugNode)parent;
            parentNode.addChild(context.indexOnParent, node);
         }
      }
      catch (DebugException e) {
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
      // Delete the whole sub tree in the business model.
      for (DeleteUndoRedoContext undoRedoContext : undoRedoContexts) {
         removeFromParent(undoRedoContext);
      }
   }
   
   /**
    * Utiltiy class to store information required for undo/redo
    * of a deletion in the business model.
    * @author Martin Hentschel
    */
   protected static class DeleteUndoRedoContext {
      /**
       * The {@link ISEDDebugNode} to delete.
       */
      private ISEDDebugNode node;
      
      /**
       * The index on the parent from that {@link #node} was removed.
       */
      private int indexOnParent;

      /**
       * Constructor.
       * @param node The {@link ISEDDebugNode} to delete.
       */
      public DeleteUndoRedoContext(ISEDDebugNode node) {
         this.node = node;
      }

      /**
       * Returns the {@link ISEDDebugNode} to delete.
       * @return The {@link ISEDDebugNode} to delete.
       */
      public ISEDDebugNode getNode() {
         return node;
      }

      /**
       * Returns the index on the parent from that {@link #node} was removed.
       * @return The index on the parent from that {@link #node} was removed.
       */
      public int getIndexOnParent() {
         return indexOnParent;
      }

      /**
       * Sets the index on the parent from that {@link #node} was removed.
       * @param indexOnParent The index on the parent from that {@link #node} was removed.
       */
      public void setIndexOnParent(int indexOnParent) {
         this.indexOnParent = indexOnParent;
      }
   }
}