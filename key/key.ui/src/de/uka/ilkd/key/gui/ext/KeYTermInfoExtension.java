package de.uka.ilkd.key.gui.ext;

import java.util.List;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.nodeviews.SequentViewInputListener;
import de.uka.ilkd.key.pp.PosInSequent;

/**
 * Extension interface for the term info string in the status line.
 *
 * @author lanzinger
 *
 * @see SequentViewInputListener
 * @see MainWindow#setStatusLine(String)
 */
public interface KeYTermInfoExtension {

    /**
    *
    * @param mainWindow the main window.
    * @param pos the position of the term whose info shall be shown.
    * @return this extension's term information.
    */
   List<String> getTermInfoStrings(MainWindow mainWindow, PosInSequent pos);

   /**
    * This extension's priority. Used for sorting.
    *
    * @return this extension's priority.
    */
   default int getPriority() {
       return 0;
   }
}
