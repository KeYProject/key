package de.uka.ilkd.key.gui.originlabels;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.api.ContextMenuKind;
import de.uka.ilkd.key.gui.extension.api.DefaultContextMenuKind;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.label.OriginTermLabel.SpecType;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.TermLabelSettings;

import javax.swing.*;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

/**
 * Extension adapter for {@link OriginTermLabel}s and {@link OriginTermLabelWindow}s.
 *
 * @author lanzinger
 */
@KeYGuiExtension.Info(name = "OriginLabels UI",
        optional = true,
        description = "UI support for origin labels" +
                "Developer: Florian Lanzinger <xxx@student.kit.edu>",
        experimental = false)
public class OriginTermLabelsExt
        implements KeYGuiExtension,
        KeYGuiExtension.ContextMenu,
        KeYGuiExtension.MainMenu,
        KeYGuiExtension.Toolbar,
        KeYGuiExtension.TermInfo {
    private ToggleTermOriginTrackingAction action;

    private ToggleTermOriginTrackingAction getAction(MainWindow mainWindow) {
        if (action == null) {
            action = new ToggleTermOriginTrackingAction(mainWindow);
        }

        return action;
    }

    @Override
    public List<Action> getMainMenuActions(MainWindow mainWindow) {
        List<Action> result = new LinkedList<>();
        result.add(getAction(mainWindow));
        return result;
    }

    @Override
    public List<Action> getContextActions(KeYMediator mediator, ContextMenuKind kind, Object underlyingObject) {
        if (kind == DefaultContextMenuKind.SEQUENT_VIEW) {
            return Collections.singletonList(new ShowOriginAction((PosInSequent) underlyingObject));
        }
        return Collections.emptyList();
    }

    @Override
    public JToolBar getToolbar(MainWindow mainWindow) {
        JToolBar tb = new JToolBar("Origin");
        JToggleButton toggle = new JToggleButton(getAction(mainWindow));

        mainWindow.getMediator().addKeYSelectionListener(new KeYSelectionListener() {

            @Override
            public void selectedProofChanged(KeYSelectionEvent e) {
                Proof proof = mainWindow.getMediator().getSelectedProof();

                if (proof != null) {
                    TermLabelSettings settings = proof.getSettings().getTermLabelSettings();
                    toggle.setSelected(settings.getUseOriginLabels());
                    settings.addSettingsListener(
                            event -> toggle.setSelected(settings.getUseOriginLabels()));
                }
            }

            @Override
            public void selectedNodeChanged(KeYSelectionEvent e) {
            }
        });

        toggle.setHideActionText(true);
        tb.add(toggle);
        return tb;
    }

    @Override
    public List<String> getTermInfoStrings(MainWindow mainWindow, PosInSequent pos) {
        PosInOccurrence pio = pos.getPosInOccurrence();
        Term term = pio.subTerm();

        OriginTermLabel originLabel =
                (OriginTermLabel) term.getLabel(OriginTermLabel.NAME);

        List<String> result = new LinkedList<>();

        // If the term has no origin label,
        // iterate over its parent terms until we find one with an origin label,
        // then show that term's origin.
        while (originLabel == null && !pio.isTopLevel()) {
            pio = pio.up();
            term = pio.subTerm();

            originLabel =
                    (OriginTermLabel) term.getLabel(OriginTermLabel.NAME);
        }

        if (originLabel != null && originLabel.getOrigin().specType != SpecType.NONE) {
            result.add("Origin: " + originLabel.getChild(0));
        }

        return result;
    }

}
