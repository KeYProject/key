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

package org.key_project.key4eclipse.common.ui.provider;

import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.key_project.key4eclipse.common.ui.util.StarterDescription;

/**
 * An {@link ILabelProvider} for {@link StarterDescription}s.
 * @author Martin Hentschel
 */
public class StarterDescriptionLabelProvider extends LabelProvider {
   /**
    * {@inheritDoc}
    */
   @Override
   public String getText(Object element) {
      if (element instanceof StarterDescription<?>) {
         return ((StarterDescription<?>)element).getName();
      }
      else {
         return super.getText(element);
      }
   }
}