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

package org.key_project.key4eclipse.starter.core.decorator;

import org.eclipse.core.resources.IFolder;
import org.eclipse.jface.viewers.IBaseLabelProvider;
import org.eclipse.jface.viewers.ILightweightLabelDecorator;
import org.eclipse.ui.PlatformUI;

/**
 * Decorates the proof folder of KeY projects.
 * @author Martin Hentschel
 */
public class ClassPathFolderLightweightLabelDecorator extends AbstractClassPathLightweightLabelDecorator {
   /**
    * The ID of this {@link ILightweightLabelDecorator}.
    */
   public static final String ID = "key_project.key4eclipse.starter.core.classPathFolderDecorator";

   /**
    * {@inheritDoc}
    */
   @Override
   protected String getBootOverlay() {
      return "icons/folder_boot_decoration.gif";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String getClassPathOverlay() {
      return "icons/folder_cp_decoration.gif";
   }
   
   /**
    * Re-decorates the given {@link IFolder}.
    * @param element The {@link IFolder} to re-decorate.
    */
   public static void redecorateFolder(IFolder folder) {
      IBaseLabelProvider decorator = PlatformUI.getWorkbench().getDecoratorManager().getBaseLabelProvider(ID);
      if (decorator instanceof ClassPathFolderLightweightLabelDecorator) {
         ((ClassPathFolderLightweightLabelDecorator) decorator).redecorate(folder);
      }
   }
}