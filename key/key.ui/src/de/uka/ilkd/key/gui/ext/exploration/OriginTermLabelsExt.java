package de.uka.ilkd.key.gui.ext.exploration;

import java.util.LinkedList;
import java.util.List;

import javax.swing.Action;
import javax.swing.JToggleButton;
import javax.swing.JToolBar;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.ext.KeYMainMenuExtension;
import de.uka.ilkd.key.gui.ext.KeYTermMenuExtension;
import de.uka.ilkd.key.gui.ext.KeYToolbarExtension;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.pp.PosInSequent;

/**
 * Extension adapter for {@link OriginTermLabel}s and {@link OriginTermLabelWindow}s.
 *
 * @author lanzinger
 */
public class OriginTermLabelsExt implements KeYTermMenuExtension, KeYMainMenuExtension, KeYToolbarExtension {

    @Override
    public List<Action> getMainMenuActions(MainWindow mainWindow) {
        List<Action> result = new LinkedList<>();
        result.add(new ToggleOriginLabelsAction(mainWindow));
        return result;
    }

    @Override
    public List<Action> getTermMenuActions(MainWindow mainWindow) {
        List<Action> result = new LinkedList<>();
        result.add(new ShowOriginAction(PosInSequent.createSequentPos()));
        return result;
    }

    @Override
    public JToolBar getToolbar(MainWindow mainWindow) {
        JToolBar tb = new JToolBar("Origin");
        JToggleButton toggle = new JToggleButton(new ToggleOriginLabelsAction(mainWindow));
        toggle.setHideActionText(true);
        tb.add(toggle);
        return tb;
    }

    @Override
    public int getPriority() {
        return 0;
    }
}
