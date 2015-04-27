package org.key_project.sed.key.core.slicing;

import java.util.HashSet;
import java.util.Set;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.model.IVariable;
import org.key_project.sed.core.annotation.ISEDAnnotationAppearance;
import org.key_project.sed.core.annotation.impl.SliceAnnotation;
import org.key_project.sed.core.annotation.impl.SliceAnnotationLink;
import org.key_project.sed.core.annotation.impl.SliceAnnotationType;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.slicing.ISEDSlicer;
import org.key_project.sed.core.util.LogUtil;
import org.key_project.sed.core.util.SEDAnnotationUtil;
import org.key_project.sed.key.core.model.IKeYSEDDebugNode;
import org.key_project.sed.key.core.model.KeYDebugTarget;
import org.key_project.sed.key.core.model.KeYVariable;
import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.symbolic_execution.slicing.AbstractSlicer;

/**
 * Provides a basic {@link ISEDSlicer} implementation which performs
 * slicing with help of an {@link AbstractSlicer}.
 * @author Martin Hentschel
 */
public abstract class AbstractKeYSlicer implements ISEDSlicer {
   /**
    * {@inheritDoc}
    */
   @Override
   public SliceAnnotation slice(ISEDDebugNode seedNode, 
                                IVariable seedVariable, 
                                ISEDAnnotationAppearance appearance,
                                IProgressMonitor monitor) throws DebugException {
      // Check if parameters are valid.
      if (seedNode instanceof IKeYSEDDebugNode<?>) {
         if (seedVariable instanceof KeYVariable) {
            IKeYSEDDebugNode<?> keySeedNode = (IKeYSEDDebugNode<?>) seedNode;
            KeYDebugTarget keyDebugTarget = keySeedNode.getDebugTarget();
            // Get needed proof elements
            Node proofSeedNode = keySeedNode.getExecutionNode().getProofNode();
            Term seedLocation = ((KeYVariable) seedVariable).getExecutionVariable().createSelectTerm();
            // Perform slicing
            AbstractSlicer slicer = createSlicer();
            ImmutableArray<Node> slices = slicer.slice(proofSeedNode, seedLocation);
            // Show slice
            SliceAnnotationType annotationType = (SliceAnnotationType)SEDAnnotationUtil.getAnnotationtype(SliceAnnotationType.TYPE_ID);
            SliceAnnotation annotation = annotationType.createAnnotation();
            if (appearance != null) {
               appearance.applyTo(annotation);
            }
            annotation.setSeed(seedVariable.getName() + " at " + seedNode.getName());
            keyDebugTarget.registerAnnotation(annotation);
            Set<IKeYSEDDebugNode<?>> linkedNodes = new HashSet<IKeYSEDDebugNode<?>>();
            for (Node slice : slices) {
               IKeYSEDDebugNode<?> keyTargetNode = keyDebugTarget.getDebugNode(slice);
               if (keyTargetNode != null) {
                  if (linkedNodes.add(keyTargetNode)) { // Ensure that nodes are linked only once
                     SliceAnnotationLink link = annotationType.createLink(annotation, keyTargetNode);
                     annotation.addLink(link);
                  }
               }
            }
            return annotation;
         }
         else {
            throw new DebugException(LogUtil.getLogger().createErrorStatus("Seed variable '" + seedVariable + "' is not supported."));
         }
      }
      else {
         throw new DebugException(LogUtil.getLogger().createErrorStatus("Seed node '" + seedNode + "' is not supported."));
      }
   }
   
   /**
    * Creates the {@link AbstractSlicer} to use.
    * @return The {@link AbstractSlicer} to use.
    */
   protected abstract AbstractSlicer createSlicer();
}
