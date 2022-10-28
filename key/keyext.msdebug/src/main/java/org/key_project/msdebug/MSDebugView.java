package org.key_project.msdebug;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.SequentInteractionListener;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.gui.sourceview.SourceView;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermImpl;
import de.uka.ilkd.key.logic.origin.OriginRef;
import de.uka.ilkd.key.pp.PosInSequent;

import javax.annotation.Nonnull;
import javax.swing.*;
import javax.swing.text.BadLocationException;
import java.awt.*;
import java.io.IOException;
import java.net.URISyntaxException;
import java.util.ArrayList;

public class MSDebugView extends JTabbedPane implements TabPanel {

    private MSDebugTab[] tabs = new MSDebugTab[0];

    private JTabbedPane pnlMain;

    public MSDebugView(@Nonnull MainWindow window, @Nonnull KeYMediator mediator) {
        super();

        tabs = new MSDebugTab[]
        {
            new OriginRefView(window, mediator),
            new SourceInsertionsView(window, mediator),
            new SourceHighlightsView(window, mediator),
        };
    }

    @Nonnull
    @Override
    public String getTitle() {
        return "MS DEBUG";
    }

    @Nonnull
    @Override
    public JComponent getComponent() {
        if (pnlMain == null)
        {
            pnlMain = new JTabbedPane();
            pnlMain.setTabPlacement(JTabbedPane.BOTTOM);
            pnlMain.setTabLayoutPolicy(JTabbedPane.SCROLL_TAB_LAYOUT);

            for (MSDebugTab t: tabs) {
                pnlMain.addTab(t.getTitle(), t);
            }
        }
        return pnlMain;
    }
}