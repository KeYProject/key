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

package org.key_project.monkey.product.ui.application;

import org.eclipse.ui.application.IWorkbenchWindowConfigurer;
import org.eclipse.ui.application.WorkbenchWindowAdvisor;

/**
 * <p>
 * Special implementation of {@link WorkbenchWindowAdvisor} for the
 * product "MonKeY".
 * </p>
 * <p>
 * For more information about RCP based products have a look at:
 * <a href="http://javawiki.sowas.com/doku.php?id=eclipse-rcp:source-example-application">http://javawiki.sowas.com/doku.php?id=eclipse-rcp:source-example-application</a>
 * </p>
 * @author Martin Hentschel
 */
public class MonKeYWorkbenchWindowAdvisor extends WorkbenchWindowAdvisor {
    /**
     * Constructor.
     * @param configurer The {@link IWorkbenchWindowConfigurer} to use.
     */
    public MonKeYWorkbenchWindowAdvisor(IWorkbenchWindowConfigurer configurer) {
        super(configurer);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void preWindowOpen() {
        IWorkbenchWindowConfigurer configurer = getWindowConfigurer();
//        configurer.setInitialSize(new Point(400, 300));
        configurer.setShowCoolBar(false);
        configurer.setShowStatusLine(false);
        configurer.setShowFastViewBars(false);
        configurer.setShowMenuBar(false);
        configurer.setShowPerspectiveBar(false);
        configurer.setShowProgressIndicator(true);
        configurer.setShowStatusLine(false);
    }
}