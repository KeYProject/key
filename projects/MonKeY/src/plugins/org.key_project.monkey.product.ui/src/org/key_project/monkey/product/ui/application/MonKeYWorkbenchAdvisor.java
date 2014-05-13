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

package org.key_project.monkey.product.ui.application;

import org.eclipse.ui.application.IWorkbenchConfigurer;
import org.eclipse.ui.application.IWorkbenchWindowConfigurer;
import org.eclipse.ui.application.WorkbenchAdvisor;
import org.eclipse.ui.application.WorkbenchWindowAdvisor;
import org.key_project.monkey.product.ui.perspective.MonKeYPerspective;

/**
 * <p>
 * Special implementation of {@link WorkbenchAdvisor} for the product "MonKeY".
 * </p>
 * <p>
 * For more information about RCP based products have a look at:
 * <a href="http://javawiki.sowas.com/doku.php?id=eclipse-rcp:source-example-application">http://javawiki.sowas.com/doku.php?id=eclipse-rcp:source-example-application</a>
 * </p> 
 * @author Martin Hentschel
 */
public class MonKeYWorkbenchAdvisor extends WorkbenchAdvisor {
    /**
     * {@inheritDoc}
     */
    @Override
    public String getInitialWindowPerspectiveId() {
        return MonKeYPerspective.ID;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void initialize(IWorkbenchConfigurer configurer) {
        super.initialize(configurer);
        configurer.setSaveAndRestore(true); // Enable state storage via IMemento
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public WorkbenchWindowAdvisor createWorkbenchWindowAdvisor(IWorkbenchWindowConfigurer configurer) {
        return new MonKeYWorkbenchWindowAdvisor(configurer);
    }
}