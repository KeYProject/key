package org.key_project.extsourceview;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.extension.api.TabPanel;

import javax.annotation.Nonnull;
import java.util.Collection;
import java.util.Collections;

@KeYGuiExtension.Info(name = "Extended Source View",
        description = "Author: Mike Schwörer <main@mikescher.com>",
        experimental = false,
        optional = true,
        priority = 10000)
public class ExtSourceViewExtension implements KeYGuiExtension, KeYGuiExtension.LeftPanel {

    @Nonnull
    @Override
    public Collection<TabPanel> getPanels(@Nonnull MainWindow window, @Nonnull KeYMediator mediator) {

        System.out.println("[EXT-SOURCE-VIEW] Initializing");

        // add a listener for changes in the proof tree
        mediator.addKeYSelectionListener(new KeYSelectionListener() {
            @Override
            public void selectedNodeChanged(KeYSelectionEvent e) {
                if (!mediator.isInAutoMode()) {
                    updateSourceview(window, mediator);
                }
            }

            @Override
            public void selectedProofChanged(KeYSelectionEvent e) {
                updateSourceview(window, mediator);
            }
        });

        return Collections.emptyList();
    }

    private void updateSourceview(MainWindow window, KeYMediator mediator) {
        System.out.println("[EXT-SOURCE-VIEW] Update");


    }
}
