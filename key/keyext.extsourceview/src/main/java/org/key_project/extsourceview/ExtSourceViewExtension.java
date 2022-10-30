package org.key_project.extsourceview;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import org.key_project.extsourceview.debug.DebugView;

import javax.annotation.Nonnull;
import java.util.Collection;
import java.util.Collections;

@KeYGuiExtension.Info(name = "Extended Source View",
        description = "Author: Mike Schwörer <main@mikescher.com>",
        experimental = false,
        optional = true,
        priority = 10000)
public class ExtSourceViewExtension implements KeYGuiExtension, KeYGuiExtension.Startup, KeYGuiExtension.LeftPanel {

    private DebugView view;


    @Override
    public void init(MainWindow window, KeYMediator mediator) {
        // add a listener for changes in the proof tree
        mediator.addKeYSelectionListener(new KeYSelectionListener() {
            @Override
            public void selectedNodeChanged(KeYSelectionEvent e) {
                if (!mediator.isInAutoMode()) {
                    SourceViewPatcher.updateSourceview(window, mediator);
                }
            }

            @Override
            public void selectedProofChanged(KeYSelectionEvent e) {
                SourceViewPatcher.updateSourceview(window, mediator);
            }
        });
    }

    @Nonnull
    @Override
    public Collection<TabPanel> getPanels(@Nonnull MainWindow window, @Nonnull KeYMediator mediator) {
        if (view == null) view = new DebugView(window, mediator);
        return Collections.singleton(view);
    }
}
