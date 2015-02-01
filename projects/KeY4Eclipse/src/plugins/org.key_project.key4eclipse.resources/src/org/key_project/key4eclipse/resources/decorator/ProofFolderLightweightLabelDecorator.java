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

import org.eclipse.core.resources.IFolder;
import org.eclipse.jface.viewers.BaseLabelProvider;
import org.eclipse.jface.viewers.IDecoration;
import org.eclipse.jface.viewers.ILightweightLabelDecorator;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.key_project.key4eclipse.resources.Activator;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;

/**
 * Decorates the proof folder of KeY projects.
 * @author Martin Hentschel
 */
public class ProofFolderLightweightLabelDecorator extends BaseLabelProvider implements ILightweightLabelDecorator {
   /**
    * {@inheritDoc}
    */
   @Override
   public void decorate(Object element, IDecoration decoration) {
      if (element instanceof IFolder && KeYResourcesUtil.isProofFolder((IFolder)element)) {
         decoration.addOverlay(AbstractUIPlugin.imageDescriptorFromPlugin(Activator.PLUGIN_ID, "icons/projectIcon.png"));
      }
   }
}