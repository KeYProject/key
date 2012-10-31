package org.key_project.monkey.product.ui.perspective;

import org.eclipse.ui.IPageLayout;
import org.eclipse.ui.IPerspectiveFactory;
import org.key_project.monkey.product.ui.view.MonKeYView;

/**
 * <p>
 * Creates the perspective "MonKeY".
 * </p>
 * <p>
 * For more information about RCP based products have a look at:
 * <a href="http://javawiki.sowas.com/doku.php?id=eclipse-rcp:source-example-application">http://javawiki.sowas.com/doku.php?id=eclipse-rcp:source-example-application</a>
 * </p>
 * @author Martin Hentschel
 */
public class MonKeYPerspective implements IPerspectiveFactory {
    /**
     * The ID of this perspective.
     */
    public static final String ID = "org.key_project.monkey.product.ui.perspective";

    /**
     * {@inheritDoc}
     */
    @Override
    public void createInitialLayout(IPageLayout layout) {
        String editorArea = layout.getEditorArea();
        layout.setEditorAreaVisible(false);
        layout.addStandaloneView(MonKeYView.ID, false, IPageLayout.TOP, 0.75f, editorArea);
        layout.addPlaceholder(IPageLayout.ID_PROGRESS_VIEW, IPageLayout.BOTTOM, 0.25f, editorArea);
    }
}
