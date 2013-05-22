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

package org.key_project.sed.ui.adapter;

import org.eclipse.core.runtime.IAdapterFactory;
import org.eclipse.debug.internal.ui.model.elements.VariableLabelProvider;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IElementLabelProvider;
import org.key_project.sed.core.model.ISEDValue;
import org.key_project.sed.core.model.ISEDVariable;
import org.key_project.sed.ui.provider.SEDVariableLabelProvider;

/**
 * This {@link IAdapterFactory} is used to return the special
 * {@link VariableLabelProvider} for {@link ISEDVariable} and {@link ISEDValue}s. 
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class SEDVariableAdapterFactory implements IAdapterFactory {
   /**
    * {@inheritDoc}
    */
   @SuppressWarnings("rawtypes")
   @Override
   public Object getAdapter(Object adaptableObject, Class adapterType) {
      if (IElementLabelProvider.class.equals(adapterType)) {
         if (adaptableObject instanceof ISEDVariable) {
            return new SEDVariableLabelProvider();
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