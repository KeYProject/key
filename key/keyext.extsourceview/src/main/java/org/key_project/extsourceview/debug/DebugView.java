package org.key_project.extsourceview.debug;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import org.key_project.extsourceview.debug.tabs.BackTransformationView;
import org.key_project.extsourceview.debug.tabs.OriginRefView;
import org.key_project.extsourceview.debug.tabs.SourceHighlightsView;
import org.key_project.extsourceview.debug.tabs.SourceInsertionsView;

import javax.annotation.Nonnull;
import javax.swing.*;

public class DebugView extends JTabbedPane implements TabPanel {

    private DebugTab[] tabs = new DebugTab[0];

    private JTabbedPane pnlMain;

    public DebugView(@Nonnull MainWindow window, @Nonnull KeYMediator mediator) {
        super();

        tabs = new DebugTab[]
        {
            new OriginRefView(window, mediator),
            new SourceInsertionsView(window, mediator),
            new SourceHighlightsView(window, mediator),
            new BackTransformationView(window, mediator),
        };
    }

    @Nonnull
    @Override
    public String getTitle() {
        return "{{DEBUG}}";
    }

    @Nonnull
    @Override
    public JComponent getComponent() {
        if (pnlMain == null)
        {
            pnlMain = new JTabbedPane();
            pnlMain.setTabPlacement(JTabbedPane.BOTTOM);
            pnlMain.setTabLayoutPolicy(JTabbedPane.SCROLL_TAB_LAYOUT);

            for (DebugTab t: tabs) {
                pnlMain.addTab(t.getTitle(), t);
            }
        }
        return pnlMain;
    }
}