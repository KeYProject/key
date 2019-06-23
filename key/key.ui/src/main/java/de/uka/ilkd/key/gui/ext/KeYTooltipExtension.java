package de.uka.ilkd.key.gui.ext;

import java.util.List;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.nodeviews.SequentView;
import de.uka.ilkd.key.pp.PosInSequent;

/**
 * Extension interface for the tooltips in the sequent view.
 *
 * @author lanzinger
 *
 * @see SequentView
 */
public interface KeYTooltipExtension {


    /**
     *
     * @param mainWindow the main window.
     * @param pos the position of the term whose info shall be shown.
     * @return this extension's term information.
     */
    List<String> getTooltipStrings(MainWindow mainWindow, PosInSequent pos);

    /**
     * This extension's priority. Used for sorting.
     *
     * @return this extension's priority.
     */
    default int getPriority() {
        return 0;
    }
}
