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
import org.key_project.sed.core.model.ISEDDebugNode;

/**
 * {@link ISection} implementation to show the constraints of an {@link ISEDDebugNode}
 * which are provided via {@link ISEDDebugNode#getConstraints()}.
 * @author Martin Hentschel
 */
public class ConstraintsNodePropertySection extends AbstractSEDDebugNodePropertySection {
   /**
    * {@inheritDoc}
    */
   @Override
   protected ISEDDebugNodeTabContent createContent() {
      return new ConstraintsTabComposite();
   }
}