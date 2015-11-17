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

package org.key_project.sed.ui.property;

import org.eclipse.ui.views.properties.tabbed.ISection;
import org.key_project.sed.core.model.ISEMethodCall;

/**
 * {@link ISection} implementation to show the method return conditions of an {@link ISEMethodCall}
 * which is provided via {@link ISEMethodCall#getMethodReturnConditions()}.
 * @author Martin Hentschel
 */
public class MethodReturnConditionsPropertySection extends AbstractSENodePropertySection {
   /**
    * {@inheritDoc}
    */
   @Override
   protected ISENodeTabContent createContent() {
      return new MethodReturnConditionsTabComposite();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean shouldUseExtraSpace() {
      return true;
   }
}