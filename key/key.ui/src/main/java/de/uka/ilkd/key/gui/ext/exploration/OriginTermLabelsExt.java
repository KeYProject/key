package de.uka.ilkd.key.gui.ext.exploration;

import java.util.Collections;
import java.util.EnumSet;
import java.util.LinkedList;
import java.util.List;

import javax.swing.Action;
import javax.swing.JToggleButton;
import javax.swing.JToolBar;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.ext.KeYMainMenuExtension;
import de.uka.ilkd.key.gui.ext.KeYSequentViewMenuExtension;
import de.uka.ilkd.key.gui.ext.KeYStatusBarExtension;
import de.uka.ilkd.key.gui.ext.KeYToolbarExtension;
import de.uka.ilkd.key.gui.ext.KeYTooltipExtension;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.label.OriginTermLabel.Origin;
import de.uka.ilkd.key.pp.PosInSequent;

/**
 * Extension adapter for {@link OriginTermLabel}s and {@link OriginTermLabelWindow}s.
 *
 * @author lanzinger
 */
public class OriginTermLabelsExt
    implements
        KeYSequentViewMenuExtension,
        KeYMainMenuExtension,
        KeYToolbarExtension,
        KeYTooltipExtension,
        KeYStatusBarExtension {

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
    public List<Action> getSequentViewMenuActions(MainWindow mainWindow, PosInSequent pos) {
        List<Action> result = new LinkedList<>();
        result.add(new ShowOriginAction(pos));
        return result;
    }

    @Override
    public EnumSet<SequentViewMenuType> getSequentViewMenuTypes() {
        return EnumSet.allOf(SequentViewMenuType.class);
    }

    @Override
    public JToolBar getToolbar(MainWindow mainWindow) {
        JToolBar tb = new JToolBar("Origin");
        JToggleButton toggle = new JToggleButton(getToggleTrackingAction(mainWindow));
        toggle.setHideActionText(true);
        tb.add(toggle);
        return tb;
    }

    @Override
    public int getPriority() {
        return 0;
    }

    @Override
    public List<String> getStatusBarStrings(MainWindow mainWindow, PosInSequent pos) {
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
