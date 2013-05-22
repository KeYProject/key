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

package org.key_project.util.test.perspective;

import org.eclipse.ui.IPageLayout;
import org.eclipse.ui.IPerspectiveFactory;

/**
 * Creates an empty perspective.
 * @author Martin Hentschel
 */
public class EmptyTestPerspectiveFactory implements IPerspectiveFactory {
   /**
    * The ID of this perspective.
    */
   public static final String PERSPECTIVE_ID = "org.key_project.util.test.perspective.EmptyTestPerspectiveFactory";
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void createInitialLayout(IPageLayout layout) {
   }
}