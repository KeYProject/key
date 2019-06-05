package de.uka.ilkd.key.gui.ext.exploration;

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
        JToggleButton toggle = new JToggleButton(getAction(mainWindow));
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
        Origin origin = OriginTermLabel.getOrigin(pos);

        List<String> result = new LinkedList<>();

        if (origin != null) {
            result.add("<b>Origin:</b> " + origin);
        }

        return result;
    }
}
