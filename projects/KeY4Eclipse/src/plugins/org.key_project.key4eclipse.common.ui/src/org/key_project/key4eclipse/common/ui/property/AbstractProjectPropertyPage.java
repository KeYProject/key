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

package org.key_project.key4eclipse.common.ui.property;

import org.eclipse.core.resources.IProject;
import org.eclipse.ui.IWorkbenchPropertyPage;
import org.eclipse.ui.dialogs.PropertyPage;

/**
 * Provides a basic implementation for a {@link PropertyPage} which works on an {@link IProject}.
 * @author Martin Hentschel
 */
public abstract class AbstractProjectPropertyPage extends PropertyPage implements IWorkbenchPropertyPage {
   /**
    * Returns the {@link IProject} that is currently configured.
    * @return The {@link IProject} to configure.
    */
   protected IProject getProject() {
       if (getElement() != null) {
           return (IProject)getElement().getAdapter(IProject.class);
       }
       else {
           return null;
       }
   }
}