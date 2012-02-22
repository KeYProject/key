package org.key_project.automaticverifier.product.ui.application;

import org.eclipse.ui.application.IWorkbenchWindowConfigurer;
import org.eclipse.ui.application.WorkbenchWindowAdvisor;

/**
 * <p>
 * Special implementation of {@link WorkbenchWindowAdvisor} for the
 * product "Automatic Verifier".
 * </p>
 * <p>
 * For more information about RCP based products have a look at:
 * <a href="http://javawiki.sowas.com/doku.php?id=eclipse-rcp:source-example-application">http://javawiki.sowas.com/doku.php?id=eclipse-rcp:source-example-application</a>
 * </p>
 * @author Martin Hentschel
 */
public class AutomaticVerifierWorkbenchWindowAdvisor extends WorkbenchWindowAdvisor {
    /**
     * Constructor.
     * @param configurer The {@link IWorkbenchWindowConfigurer} to use.
     */
    public AutomaticVerifierWorkbenchWindowAdvisor(IWorkbenchWindowConfigurer configurer) {
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