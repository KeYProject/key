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

package org.key_project.key4eclipse.resources.decorator;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.viewers.BaseLabelProvider;
import org.eclipse.jface.viewers.IBaseLabelProvider;
import org.eclipse.jface.viewers.IDecoration;
import org.eclipse.jface.viewers.ILightweightLabelDecorator;
import org.eclipse.jface.viewers.LabelProviderChangedEvent;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PlatformUI;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.key4eclipse.resources.util.LogUtil;

/**
 * Decorates the proof folder of KeY projects.
 * @author Martin Hentschel
 */
public class ProofFileLightweightLabelDecorator extends BaseLabelProvider implements ILightweightLabelDecorator {
   /**
    * The ID of this {@link ILightweightLabelDecorator}.
    */
   public static final String ID = "org.key_project.key4eclipse.resources.proofFilesDecorator";
   
   /**
    * Re-decorates the given proof file.
    * @param element The proof file to re-decorate.
    */
   public static void redecorateProofFile(IFile proofFile) {
      IBaseLabelProvider decorator = PlatformUI.getWorkbench().getDecoratorManager().getBaseLabelProvider(ID);
      if (decorator instanceof ProofFileLightweightLabelDecorator) {
         ((ProofFileLightweightLabelDecorator) decorator).redecorate(proofFile);
      }
   }
   
   /**
    * Re-decorates the given element.
    * @param element The element to re-decorate.
    */
   public void redecorate(Object element) {
      fireLabelProviderChanged(new LabelProviderChangedEvent(this, element));
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void decorate(Object element, IDecoration decoration) {
      try {
         if (element instanceof IFile) {
            IFile file = (IFile) element;
            Boolean inCycle = KeYResourcesUtil.isProofInRecursionCycle(file);
            if (inCycle != null && inCycle.booleanValue()) {
               decoration.addOverlay(PlatformUI.getWorkbench().getSharedImages().getImageDescriptor(ISharedImages.IMG_DEC_FIELD_ERROR), IDecoration.TOP_RIGHT);
            }
            else {
               Boolean closed = KeYResourcesUtil.isProofClosed(file);
               if (closed != null && !closed.booleanValue()) {
                  decoration.addOverlay(PlatformUI.getWorkbench().getSharedImages().getImageDescriptor(ISharedImages.IMG_DEC_FIELD_WARNING), IDecoration.TOP_RIGHT);
               }
            }
         }
      }
      catch (CoreException e) {
         LogUtil.getLogger().logError(e);
      }
   }
}