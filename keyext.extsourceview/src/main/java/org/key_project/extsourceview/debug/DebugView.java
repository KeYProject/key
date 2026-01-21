package org.key_project.extsourceview.debug;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import org.key_project.extsourceview.debug.tabs.*;

import javax.annotation.Nonnull;
import javax.swing.*;

/**
 * Class for the DEBUG panel of this plugin (actual UI is implemented in the different tabs)
 */
public class DebugView extends JTabbedPane implements TabPanel {

    private final DebugTab[] tabs;

    public final OriginRefView OriginRefView;
    public final SourceInsertionsView SourceInsertionsView;
    public final SourceHighlightsView SourceHighlightsView;
    public final BackTransformationView BackTransformationView;
    public final JavaPosView JavaPosView;
    public final HeapSourceView HeapSourceView;

    private JTabbedPane pnlMain;

    public DebugView(@Nonnull MainWindow window, @Nonnull KeYMediator mediator) {
        super();

        tabs = new DebugTab[]
        {
            OriginRefView = new OriginRefView(window, mediator),
            SourceInsertionsView = new SourceInsertionsView(window, mediator),
            SourceHighlightsView = new SourceHighlightsView(window, mediator),
            BackTransformationView = new BackTransformationView(window, mediator),
            JavaPosView = new JavaPosView(window, mediator),
            HeapSourceView = new HeapSourceView(window, mediator),
        };
    }

    @Nonnull
    @Override
    public String getTitle() {
        return "ExtSourceView {{DEBUG}}";
    }

    @Nonnull
    @Override
    public JComponent getComponent() {
        if (pnlMain == null) {
            pnlMain = new JTabbedPane();
            pnlMain.setTabPlacement(JTabbedPane.BOTTOM);
            pnlMain.setTabLayoutPolicy(JTabbedPane.SCROLL_TAB_LAYOUT);

            for (DebugTab t : tabs) {
                pnlMain.addTab(t.getTitle(), t);
            }

            pnlMain.setSelectedIndex(3);
        }
        return pnlMain;
    }
}
