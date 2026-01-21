package org.key_project.extsourceview;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.gui.sourceview.SourceClickedListener;
import de.uka.ilkd.key.gui.sourceview.SourceView;
import de.uka.ilkd.key.gui.sourceview.SourceViewInsertion;
import org.key_project.extsourceview.debug.DebugView;
import org.key_project.extsourceview.transformer.InternTransformException;
import org.key_project.extsourceview.transformer.TransformException;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.awt.event.MouseEvent;
import java.util.Collection;
import java.util.Collections;

@KeYGuiExtension.Info(name = "Extended Source View",
    description = "Author: Mike Schwörer <main@mikescher.com>", experimental = false,
    optional = true, priority = 10000)
public class ExtSourceViewExtension
        implements KeYGuiExtension, KeYGuiExtension.Startup, KeYGuiExtension.LeftPanel, SourceClickedListener {

    private static final Logger LOGGER = LoggerFactory.getLogger(ExtSourceViewExtension.class);

    public static ExtSourceViewExtension Inst;

    private DebugView view;

    public boolean ShowNonRelevantTerms            = false;
    public boolean RecursiveOriginLookup           = false;
    public boolean AllowUntaggedFormulas           = false;
    public boolean NoTranslationFallback           = false;
    public int     PositioningStrategy             = 3;
    public int     ScrollFixMode                   = 2;
    public boolean TransformerEnabled              = true;
    public boolean ColorizedInsTerms               = true;
    public boolean ShowExtInteractions             = false;
    public boolean FailOnCategorization            = false;
    public boolean FailOnTranslation               = false;
    public boolean FailOnPositioning               = false;
    public boolean AllowUnknownConstants           = true;
    public boolean AllowDisjunctAssertions         = true;
    public boolean ReInlineConstPullouts           = true;
    public boolean ManuallyTranslateLoopAssertions = true;

    public MainWindow window;
    public KeYMediator mediator;

    public ExtSourceViewExtension() {
        Inst = this;
    }

    @Override
    public void init(MainWindow window, KeYMediator mediator) {
        if (view == null)
            view = new DebugView(window, mediator);

        this.window = window;
        this.mediator = mediator;

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
    public Collection<TabPanel> getPanels(@Nonnull MainWindow window,
            @Nonnull KeYMediator mediator) {
        if (view == null)
            view = new DebugView(window, mediator);

        return Collections.singleton(view);
    }

    public void update(MainWindow window, KeYMediator mediator) {
        if (mediator.getSelectedProof() == null || window.getSourceViewFrame().getSourceView().getSelectedFile() == null) {
            view.BackTransformationView.clearStatus();
            return;
        }

        try {
            SourceViewPatcher.updateSourceview(
                    window,
                    mediator,
                    TransformerEnabled,
                    !ShowNonRelevantTerms,
                    FailOnCategorization,
                    FailOnTranslation,
                    FailOnPositioning,
                    RecursiveOriginLookup,
                    AllowUntaggedFormulas,
                    !NoTranslationFallback,
                    PositioningStrategy,
                    ColorizedInsTerms,
                    AllowUnknownConstants,
                    AllowDisjunctAssertions,
                    ReInlineConstPullouts,
                    ManuallyTranslateLoopAssertions,
                    ScrollFixMode);

            view.BackTransformationView.clearStatus();
        } catch (TransformException e) {
            // failed to transform sequent
            view.BackTransformationView.clearStatus();
            SourceViewPatcher.clearInsertions(window);
            view.BackTransformationView.setStatusFailure(mediator.getServices(), mediator.getSelectedNode().sequent(), e);
        } catch (InternTransformException e) {
            // some kind of internal error happened?
            view.BackTransformationView.clearStatus();
            LOGGER.error("error while updateing ext-sourceview", e);
            view.BackTransformationView.setStatusException(e);
        }

        SourceView sourceView = window.getSourceViewFrame().getSourceView();

        sourceView.removeSourceClickedListener(this);
        sourceView.addSourceClickedListener(this);

    }

    @Override
    public void sourceClicked(@Nullable SourceViewInsertion insertion, MouseEvent e) {
        if (insertion == null && e.getButton() == MouseEvent.BUTTON3) {
            SourceViewPatcher.showInteractionContextMenu(mediator, null, e);
        }
    }
}
