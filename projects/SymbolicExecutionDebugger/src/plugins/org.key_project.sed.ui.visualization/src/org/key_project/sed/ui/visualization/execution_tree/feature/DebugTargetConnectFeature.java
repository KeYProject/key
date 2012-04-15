package org.key_project.sed.ui.visualization.execution_tree.feature;

import org.eclipse.debug.core.DebugException;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.IRemoveFeature;
import org.eclipse.graphiti.features.IUpdateFeature;
import org.eclipse.graphiti.features.context.ICustomContext;
import org.eclipse.graphiti.features.context.IRemoveContext;
import org.eclipse.graphiti.features.context.impl.RemoveContext;
import org.eclipse.graphiti.features.custom.AbstractCustomFeature;
import org.eclipse.graphiti.features.custom.ICustomFeature;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.ui.visualization.util.LogUtil;

/**
 * An {@link ICustomFeature} that connects the given {@link Diagram}
 * with specified {@link ISEDDebugTarget}s. The {@link ISEDDebugTarget}
 * are specified via property {@link #PROPERTY_DEBUG_TARGETS} of the given
 * {@link ICustomContext}.
 * @author Martin Hentschel
 */
public class DebugTargetConnectFeature extends AbstractCustomFeature {
   /**
    * Property for an {@link ISEDDebugTarget} array which contains
    * the {@link ISEDDebugTarget} to link with {@link #getDiagram()}.
    */   
   public static final String PROPERTY_DEBUG_TARGETS = "debugTargets";

   /**
    * Indicates that changes were made in {@link #execute(ICustomContext)} or not.
    */
   private boolean changesDone = false;
   
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link IUpdateFeature}.
    */
   public DebugTargetConnectFeature(IFeatureProvider fp) {
      super(fp);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getDescription() {
      return "Creates a connection between this diagram and the specified debug targets.";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() {
      return "Connect diagram with debug targets";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canExecute(ICustomContext context) {
      Object obj = context.getProperty(PROPERTY_DEBUG_TARGETS);
      return obj instanceof ISEDDebugTarget[];
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void execute(ICustomContext context) {
      try {
         Object obj = context.getProperty(PROPERTY_DEBUG_TARGETS);
         if (obj instanceof ISEDDebugTarget[]) {
            // Clear diagram
            Object[] oldLinkedObjects = getAllBusinessObjectsForPictogramElement(getDiagram());
            for (Object oldObj : oldLinkedObjects) {
               if (oldObj instanceof ISEDDebugTarget) {
                  ISEDThread[] threads = ((ISEDDebugTarget)oldObj).getSymbolicThreads();
                  for (ISEDThread thread : threads) {
                     PictogramElement[] elements = getFeatureProvider().getAllPictogramElementsForBusinessObject(thread);
                     for (PictogramElement pictogramElement : elements) {
                        IRemoveContext removeContext = new RemoveContext(pictogramElement);
                        IRemoveFeature feature = getFeatureProvider().getRemoveFeature(removeContext);
                        feature.execute(removeContext);
                     }
                  }
               }
            }
            // Recreate diagram with new content
            link(getDiagram(), (ISEDDebugTarget[])obj);
            updatePictogramElement(getDiagram());
            changesDone = true;
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
   public boolean hasDoneChanges() {
      return changesDone;
   }
}
