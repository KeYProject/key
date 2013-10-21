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

package org.key_project.sed.ui.presentation;

import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.model.IValue;
import org.eclipse.debug.ui.IDebugModelPresentation;
import org.eclipse.debug.ui.IValueDetailListener;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDValue;
import org.key_project.sed.core.model.ISEDVariable;
import org.key_project.sed.ui.util.LogUtil;
import org.key_project.sed.ui.util.SEDImages;
import org.key_project.util.java.StringUtil;

/**
 * Provides a basic implementation of {@link IDebugModelPresentation} 
 * for a Symbolic Execution Debugger (SED).
 * @author Martin Hentschel
 */
public abstract class AbstractSEDDebugModelPresentation extends LabelProvider implements IDebugModelPresentation {
   /**
    * {@inheritDoc}
    */
   @Override
   public void setAttribute(String attribute, Object value) {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void computeDetail(IValue value, IValueDetailListener listener) {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getText(Object element) {
      try {
         if (element instanceof ISEDDebugNode) {
            String name = ((ISEDDebugNode)element).getName();
            return StringUtil.toSingleLinedString(name);
         }
         else if (element instanceof ISEDVariable) { // Used if no columns are shown in the variables view
            String name = ((ISEDVariable)element).getName();
            return StringUtil.toSingleLinedString(name);
         }
         else if (element instanceof ISEDValue) { // Used if no columns are shown in the variables view
            String valueString = ((ISEDValue)element).getValueString();
            return StringUtil.toSingleLinedString(valueString);
         }
         else {
            return null; // Text is computed somewhere else in the Eclipse Debug API.
         }
      }
      catch (DebugException e) {
         LogUtil.getLogger().logError(e);
         return null; // Text is computed somewhere else in the Eclipse Debug API.
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Image getImage(Object element) {
      if (element instanceof ISEDDebugNode) {
         return SEDImages.getNodeImage((ISEDDebugNode)element);
      }
      else {
         return super.getImage(element);
      }
   }
}