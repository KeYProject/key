package org.key_project.extsourceview;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import org.key_project.extsourceview.debug.DebugView;
import org.key_project.extsourceview.transformer.InternTransformException;
import org.key_project.extsourceview.transformer.TransformException;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.annotation.Nonnull;
import javax.swing.*;
import java.util.Collection;
import java.util.Collections;

@KeYGuiExtension.Info(name = "Extended Source View",
        description = "Author: Mike Schwörer <main@mikescher.com>",
        experimental = false,
        optional = true,
        priority = 10000)
public class ExtSourceViewExtension implements KeYGuiExtension, KeYGuiExtension.Startup, KeYGuiExtension.LeftPanel {

    private static final Logger LOGGER = LoggerFactory.getLogger(ExtSourceViewExtension.class);

    public static ExtSourceViewExtension Inst;

    private DebugView view;

    public boolean HideNonRelevantTerms = true;
    public boolean ContinueInError = false;

    public ExtSourceViewExtension() {
        Inst = this;
    }

    @Override
    public void init(MainWindow window, KeYMediator mediator) {
        if (view == null) view = new DebugView(window, mediator);

        mediator.addKeYSelectionListener(new KeYSelectionListener() {
            @Override
            public void selectedNodeChanged(KeYSelectionEvent e) {
                if (!mediator.isInAutoMode()) {
                    update(window, mediator);
                }
            }

            @Override
            public void selectedProofChanged(KeYSelectionEvent e) {
                update(window, mediator);
            }
        });
    }

    @Nonnull
    @Override
    public Collection<TabPanel> getPanels(@Nonnull MainWindow window, @Nonnull KeYMediator mediator) {
        if (view == null) view = new DebugView(window, mediator);

        return Collections.singleton(view);
    }

    public void update(MainWindow window, KeYMediator mediator) {
        try {
            SourceViewPatcher.updateSourceview(window, mediator, HideNonRelevantTerms, ContinueInError);
            view.BackTransformationView.clearStatus();
        } catch (TransformException e) {
            // failed to transform sequent
            view.BackTransformationView.setStatusFailure(e);
        } catch (InternTransformException e) {
            // some kind of internal error happened?
            LOGGER.error("error while updateing ext-sourceview", e);
            view.BackTransformationView.setStatusException(e);
            JOptionPane.showMessageDialog(window, e.toString(), "ERROR WHIE UPDATING SV", JOptionPane.ERROR_MESSAGE);
        }
    }
}
