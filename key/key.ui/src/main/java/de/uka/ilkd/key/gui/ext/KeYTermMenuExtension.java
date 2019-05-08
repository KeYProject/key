package de.uka.ilkd.key.gui.ext;

import java.util.List;

import javax.swing.Action;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.pp.PosInSequent;

/**
 * @author Alexander Weigl <weigl@kit.edu>
 */
public interface KeYTermMenuExtension {
    /**
     * @param mainWindow non-null
     * @param pos the position which the user selected
     * @return a list of actions
     */
    List<Action> getTermMenuActions(MainWindow mainWindow, PosInSequent pos);
}
