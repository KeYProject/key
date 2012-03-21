package org.key_project.automaticverifier.product.ui.perspective;

import org.eclipse.ui.IPageLayout;
import org.eclipse.ui.IPerspectiveFactory;
import org.key_project.automaticverifier.product.ui.view.AutomaticVerifierView;

/**
 * <p>
 * Creates the perspective "Automatic Verifier".
 * </p>
 * <p>
 * For more information about RCP based products have a look at:
 * <a href="http://javawiki.sowas.com/doku.php?id=eclipse-rcp:source-example-application">http://javawiki.sowas.com/doku.php?id=eclipse-rcp:source-example-application</a>
 * </p>
 * @author Martin Hentschel
 */
public class AutomaticVerifierPerspective implements IPerspectiveFactory {
    /**
     * The ID of this perspective.
     */
    public static final String ID = "org.key_project.automaticverifier.perspective";

    /**
     * {@inheritDoc}
     */
    @Override
    public void createInitialLayout(IPageLayout layout) {
        String editorArea = layout.getEditorArea();
        layout.setEditorAreaVisible(false);
        layout.addStandaloneView(AutomaticVerifierView.ID, false, IPageLayout.TOP, 0.75f, editorArea);
        layout.addPlaceholder(IPageLayout.ID_PROGRESS_VIEW, IPageLayout.BOTTOM, 0.25f, editorArea);
    }
}
