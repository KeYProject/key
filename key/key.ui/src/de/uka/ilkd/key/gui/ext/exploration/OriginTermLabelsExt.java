package de.uka.ilkd.key.gui.ext.exploration;

import java.util.LinkedList;
import java.util.List;

import javax.swing.Action;
import javax.swing.JToggleButton;
import javax.swing.JToolBar;

import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.ext.KeYMainMenuExtension;
import de.uka.ilkd.key.gui.ext.KeYTermInfoExtension;
import de.uka.ilkd.key.gui.ext.KeYTermMenuExtension;
import de.uka.ilkd.key.gui.ext.KeYToolbarExtension;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.label.OriginTermLabel.SpecType;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.TermLabelSettings;

/**
 * Extension adapter for {@link OriginTermLabel}s and {@link OriginTermLabelWindow}s.
 *
 * @author lanzinger
 */
public class OriginTermLabelsExt
    implements
        KeYTermMenuExtension,
        KeYMainMenuExtension,
        KeYToolbarExtension,
        KeYTermInfoExtension {

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
    public List<Action> getTermMenuActions(MainWindow mainWindow, PosInSequent pos) {
        List<Action> result = new LinkedList<>();
        result.add(new ShowOriginAction(pos));
        return result;
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
            public void selectedNodeChanged(KeYSelectionEvent e) { }
        });

        toggle.setHideActionText(true);
        tb.add(toggle);
        return tb;
    }

    @Override
    public int getPriority() {
        return 0;
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
