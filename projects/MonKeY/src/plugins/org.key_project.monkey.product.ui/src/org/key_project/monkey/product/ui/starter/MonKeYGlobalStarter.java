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

package org.key_project.monkey.product.ui.starter;

import org.key_project.key4eclipse.common.ui.starter.IGlobalStarter;
import org.key_project.monkey.product.ui.perspective.MonKeYPerspective;
import org.key_project.util.eclipse.WorkbenchUtil;

/**
 * Starts MonKeY which means that the MonKeY perspective is opened.
 * @author Martin Hentschel
 */
public class MonKeYGlobalStarter implements IGlobalStarter {
   /**
    * {@inheritDoc}
    */
   @Override
   public void open() throws Exception {
      WorkbenchUtil.openPerspective(MonKeYPerspective.ID);
   }
}