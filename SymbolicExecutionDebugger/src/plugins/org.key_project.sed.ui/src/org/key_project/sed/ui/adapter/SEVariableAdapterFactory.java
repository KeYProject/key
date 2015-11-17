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

package org.key_project.sed.ui.adapter;

import org.eclipse.core.runtime.IAdapterFactory;
import org.eclipse.debug.internal.ui.model.elements.VariableLabelProvider;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IElementLabelProvider;
import org.key_project.sed.core.model.ISEValue;
import org.key_project.sed.core.model.ISEVariable;
import org.key_project.sed.ui.provider.SEVariableLabelProvider;

/**
 * This {@link IAdapterFactory} is used to return the special
 * {@link VariableLabelProvider} for {@link ISEVariable} and {@link ISEValue}s. 
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class SEVariableAdapterFactory implements IAdapterFactory {
   /**
    * {@inheritDoc}
    */
   @SuppressWarnings("rawtypes")
   @Override
   public Object getAdapter(Object adaptableObject, Class adapterType) {
      if (IElementLabelProvider.class.equals(adapterType)) {
         if (adaptableObject instanceof ISEVariable) {
            return new SEVariableLabelProvider();
         }
         else {
            return new VariableLabelProvider();
         }
      }
      else {
         return null;
      }
   }

   /**
    * {@inheritDoc}
    */
   @SuppressWarnings("rawtypes")
   @Override
   public Class[] getAdapterList() {
      return new Class[] {IElementLabelProvider.class};
   }
}