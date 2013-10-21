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

package org.key_project.sed.ui.property;

import org.eclipse.swt.widgets.Composite;
import org.key_project.sed.core.model.ISEDDebugNode;

/**
 * Provides the basic functionalities for a content {@link Composite}
 * shown in an {@link AbstractSEDDebugNodePropertySection}.
 * @author Martin Hentschel
 */
public abstract class AbstractSEDDebugNodeTabComposite extends Composite {
   /**
    * Constructor.
    * @param parent The parent {@link Composite}.
    * @param style The style to use.
    */
   public AbstractSEDDebugNodeTabComposite(Composite parent, int style) {
      super(parent, style);
   }

   /**
    * Updates the shown content.
    * @param node The {@link ISEDDebugNode} which provides the new content.
    */
   public abstract void updateContent(ISEDDebugNode node);
}