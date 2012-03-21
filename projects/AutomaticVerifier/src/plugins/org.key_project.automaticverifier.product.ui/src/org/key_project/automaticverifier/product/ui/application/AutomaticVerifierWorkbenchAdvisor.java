package org.key_project.automaticverifier.product.ui.application;

import org.eclipse.ui.application.IWorkbenchConfigurer;
import org.eclipse.ui.application.IWorkbenchWindowConfigurer;
import org.eclipse.ui.application.WorkbenchAdvisor;
import org.eclipse.ui.application.WorkbenchWindowAdvisor;
import org.key_project.automaticverifier.product.ui.perspective.AutomaticVerifierPerspective;

/**
 * <p>
 * Special implementation of {@link WorkbenchAdvisor} for the
 * product "Automatic Verifier".
 * </p>
 * <p>
 * For more information about RCP based products have a look at:
 * <a href="http://javawiki.sowas.com/doku.php?id=eclipse-rcp:source-example-application">http://javawiki.sowas.com/doku.php?id=eclipse-rcp:source-example-application</a>
 * </p> 
 * @author Martin Hentschel
 */
public class AutomaticVerifierWorkbenchAdvisor extends WorkbenchAdvisor {
    /**
     * {@inheritDoc}
     */
    @Override
    public String getInitialWindowPerspectiveId() {
        return AutomaticVerifierPerspective.ID;
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
        return new AutomaticVerifierWorkbenchWindowAdvisor(configurer);
    }
}
