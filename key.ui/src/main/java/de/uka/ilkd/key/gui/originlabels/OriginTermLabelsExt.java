/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.originlabels;

import java.awt.event.ActionEvent;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.stream.Collectors;
import javax.swing.Action;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.NodeInfoVisualizer;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.extension.api.ContextMenuKind;
import de.uka.ilkd.key.gui.extension.api.DefaultContextMenuKind;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.label.OriginTermLabel.Origin;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Node;

/**
 * Extension adapter for {@link OriginTermLabel}s and {@link OriginTermLabelVisualizer}s.
 *
 * @author lanzinger
 */
@KeYGuiExtension.Info(name = "Origin Tracking", optional = true,
    description = "UI support for origin tracking", experimental = false)
public class OriginTermLabelsExt implements KeYGuiExtension, KeYGuiExtension.ContextMenu,
        KeYGuiExtension.Tooltip, KeYGuiExtension.MainMenu, KeYGuiExtension.TermInfo {

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
    public List<Action> getContextActions(KeYMediator mediator, ContextMenuKind kind,
            Object underlyingObject) {
        if (kind == DefaultContextMenuKind.SEQUENT_VIEW) {
            return Collections.singletonList(new ShowOriginAction((PosInSequent) underlyingObject));
        } else if (kind == DefaultContextMenuKind.PROOF_TREE && underlyingObject instanceof Node) {
            Node node = (Node) underlyingObject;
            return NodeInfoVisualizer.getInstances(node).stream().map(OpenVisualizerAction::new)
                    .collect(Collectors.toList());
        } else {
            return Collections.emptyList();
        }
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

        OriginTermLabel label =
            pio == null ? null : (OriginTermLabel) pio.subTerm().getLabel(OriginTermLabel.NAME);

        if (label != null && !label.getSubtermOrigins().isEmpty()) {
            result += "<b>Origin of (former) sub-terms:</b><br>" + label.getSubtermOrigins()
                    .stream().map(o -> o + "<br>").reduce("", String::concat);
        }

        List<String> resultList = new LinkedList<>();
        resultList.add(result);
        return resultList;
    }

    private static final class OpenVisualizerAction extends KeyAction {

        private static final long serialVersionUID = -2936000510977056583L;
        /** The visualizer shown by this action. */
        private final NodeInfoVisualizer vis;

        private OpenVisualizerAction(NodeInfoVisualizer vis) {
            setName(vis.getLongName());
            setMenuPath("Windows");
            setIcon(IconFactory.WINDOW_ICON.get());

            this.vis = vis;
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            MainWindow.getInstance().getSourceViewFrame().toFront(vis);
        }
    }
}
