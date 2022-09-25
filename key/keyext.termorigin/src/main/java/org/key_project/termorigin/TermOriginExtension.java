package org.key_project.termorigin;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.extension.api.TabPanel;

import javax.annotation.Nonnull;
import java.util.Collection;
import java.util.Collections;

@KeYGuiExtension.Info(name = "TermOrigin",
        description = "Author: Mike Schwörer <main@mikescher.com>",
        experimental = false,
        optional = true,
        priority = 10000)
public class TermOriginExtension implements KeYGuiExtension, KeYGuiExtension.LeftPanel {

    private TermOriginView view;

    @Nonnull
    @Override
    public Collection<TabPanel> getPanels(@Nonnull MainWindow window, @Nonnull KeYMediator mediator) {
        if (view == null) view = new TermOriginView(window, mediator);
        return Collections.singleton(view);
    }
}
