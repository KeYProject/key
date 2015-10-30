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
import org.key_project.sed.core.model.ISEBaseMethodReturn;

/**
 * {@link ISection} implementation to show the call state of an {@link ISEBaseMethodReturn}
 * which is provided via {@link ISEBaseMethodReturn#getCallStateVariables()}.
 * @author Martin Hentschel
 */
public class CallStatePropertySection extends AbstractSENodePropertySection {
   /**
    * {@inheritDoc}
    */
   @Override
   protected ISENodeTabContent createContent() {
      return new CallStateTabComposite();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean shouldUseExtraSpace() {
      return true;
   }
}