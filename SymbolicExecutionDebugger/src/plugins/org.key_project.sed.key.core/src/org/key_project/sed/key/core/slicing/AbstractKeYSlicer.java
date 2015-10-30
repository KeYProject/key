package org.key_project.sed.key.core.slicing;

import java.util.HashSet;
import java.util.Set;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.model.IVariable;
import org.key_project.sed.core.annotation.ISEAnnotationAppearance;
import org.key_project.sed.core.annotation.impl.SliceAnnotation;
import org.key_project.sed.core.annotation.impl.SliceAnnotationLink;
import org.key_project.sed.core.annotation.impl.SliceAnnotationType;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.slicing.ISESlicer;
import org.key_project.sed.core.util.LogUtil;
import org.key_project.sed.core.util.SEAnnotationUtil;
import org.key_project.sed.key.core.model.IKeYSENode;
import org.key_project.sed.key.core.model.KeYDebugTarget;
import org.key_project.sed.key.core.model.KeYVariable;
import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.slicing.AbstractSlicer;

/**
 * Provides a basic {@link ISESlicer} implementation which performs
 * slicing with help of an {@link AbstractSlicer}.
 * @author Martin Hentschel
 */
public abstract class AbstractKeYSlicer implements ISESlicer {
   /**
    * {@inheritDoc}
    */
   @Override
   public SliceAnnotation slice(ISENode seedNode, 
                                IVariable seedVariable, 
                                ISEAnnotationAppearance appearance,
                                IProgressMonitor monitor) throws DebugException {
      try {
         // Check if parameters are valid.
         if (seedNode instanceof IKeYSENode<?>) {
            if (seedVariable instanceof KeYVariable) {
               IKeYSENode<?> keySeedNode = (IKeYSENode<?>) seedNode;
               KeYDebugTarget keyDebugTarget = keySeedNode.getDebugTarget();
               // Get needed proof elements
               Node proofSeedNode = keySeedNode.getExecutionNode().getProofNode();
               Term seedLocation = ((KeYVariable) seedVariable).getExecutionVariable().createSelectTerm();
               // Perform slicing
               AbstractSlicer slicer = createSlicer();
               ImmutableArray<Node> slices = slicer.slice(proofSeedNode, seedLocation);
               // Show slice
               SliceAnnotationType annotationType = (SliceAnnotationType)SEAnnotationUtil.getAnnotationtype(SliceAnnotationType.TYPE_ID);
               SliceAnnotation annotation = annotationType.createAnnotation();
               if (appearance != null) {
                  appearance.applyTo(annotation);
               }
               annotation.setSeed(seedVariable.getName() + " at " + seedNode.getName());
               keyDebugTarget.registerAnnotation(annotation);
               Set<IKeYSENode<?>> linkedNodes = new HashSet<IKeYSENode<?>>();
               for (Node slice : slices) {
                  IKeYSENode<?> keyTargetNode = keyDebugTarget.getDebugNode(slice);
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
      catch (ProofInputException e) {
         throw new DebugException(LogUtil.getLogger().createErrorStatus(e));
      }
   }
   
   /**
    * Creates the {@link AbstractSlicer} to use.
    * @return The {@link AbstractSlicer} to use.
    */
   protected abstract AbstractSlicer createSlicer();
}
