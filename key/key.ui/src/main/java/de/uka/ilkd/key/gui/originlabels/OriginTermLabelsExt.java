package de.uka.ilkd.key.gui.originlabels;

import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import javax.swing.Action;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.api.ContextMenuKind;
import de.uka.ilkd.key.gui.extension.api.DefaultContextMenuKind;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.label.OriginTermLabel.Origin;
import de.uka.ilkd.key.pp.PosInSequent;

/**
 * Extension adapter for {@link OriginTermLabel}s and {@link OriginTermLabelWindow}s.
 *
 * @author lanzinger
 */
@KeYGuiExtension.Info(name = "OriginLabels UI",
        optional = true,
        description = "UI support for origin labels",
        experimental = false)
public class OriginTermLabelsExt
        implements KeYGuiExtension,
        KeYGuiExtension.ContextMenu,
        KeYGuiExtension.Tooltip,
        KeYGuiExtension.MainMenu,
        KeYGuiExtension.TermInfo {

    /** @see ToggleTermOriginTrackingAction */
    private ToggleTermOriginTrackingAction toggleTrackingAction;

    /** @see ToggleOriginHighlightAction */
    private ToggleOriginHighlightAction toggleSourceViewHighlightAction;

    private ToggleTermOriginTrackingAction getToggleTrackingAction(MainWindow mainWindow) {
        if (toggleTrackingAction == null) {
            toggleTrackingAction = new ToggleTermOriginTrackingAction(mainWindow);
        }

        return toggleTrackingAction;
    }

    private ToggleOriginHighlightAction getToggleSourceViewHighlightAction(MainWindow mainWindow) {
        if (toggleSourceViewHighlightAction == null) {
            toggleSourceViewHighlightAction = new ToggleOriginHighlightAction(mainWindow);
        }

        return toggleSourceViewHighlightAction;
    }

    @Override
    public List<Action> getMainMenuActions(MainWindow mainWindow) {
        List<Action> result = new LinkedList<>();
        result.add(getToggleTrackingAction(mainWindow));
        result.add(getToggleSourceViewHighlightAction(mainWindow));
        return result;
    }

    @Override
    public List<Action> getContextActions(
            KeYMediator mediator,
            ContextMenuKind kind,
            Object underlyingObject) {
        if (kind == DefaultContextMenuKind.SEQUENT_VIEW) {
            return Collections.singletonList(new ShowOriginAction((PosInSequent) underlyingObject));
        } else if (kind == DefaultContextMenuKind.PROOF_TREE) {

        }
        return Collections.emptyList();
    }

    @Override
    public List<String> getTermInfoStrings(MainWindow mainWindow, PosInSequent pos) {
        Origin origin = OriginTermLabel.getOrigin(pos);

        List<String> result = new LinkedList<>();

        if (origin != null) {
            result.add("Origin: " + origin);
        }

        return result;
    }

    @Override
    public List<String> getTooltipStrings(MainWindow mainWindow, PosInSequent pos) {
        if (pos == null || pos.isSequent()) {
            return Collections.emptyList();
        }

        Origin origin = OriginTermLabel.getOrigin(pos);

        String result = "";

        if (origin != null) {
            result += "<b>Origin:</b> " + origin + "<br>";
        }

        PosInOccurrence pio = pos.getPosInOccurrence();

        OriginTermLabel label = pio == null ? null : (OriginTermLabel) pio
                .subTerm().getLabel(OriginTermLabel.NAME);

        if (label != null && !label.getSubtermOrigins().isEmpty()) {
            result += "<b>Origin of (former) sub-terms:</b><br>" +
                    label.getSubtermOrigins().stream()
                    .map(o -> "" + o + "<br>").reduce("", String::concat);
        }

        List<String> resultList = new LinkedList<>();
        resultList.add(result);
        return resultList;
    }
}
