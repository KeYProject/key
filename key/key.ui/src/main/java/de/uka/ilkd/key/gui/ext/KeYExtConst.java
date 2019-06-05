package de.uka.ilkd.key.gui.ext;

import java.util.Iterator;

import javax.swing.JMenu;

/**
 * Constants used in the KeY GUI Extensions.
 *
 * @author Alexander Weigl <weigl@kit.edu>
 */
public interface KeYExtConst {

    /**
     * Additional key for {@link javax.swing.Action}s. Describes the priority,
     * and therefor an order to arrange these actions.
     */
    String PRIORITY = "PRIORITY";

    /**
     * Additional key for {@link javax.swing.Action}s. Describes a path in a menu
     * where an action should be injected in.
     * <p>
     * The path should be a dot-separated string, i.e. "Heatmap.Options" would inject an action
     * into a sub-sub Menu Options below Heatmap.
     *
     * @see KeYGuiExtensionFacade#findMenu(JMenu, Iterator)
     */
    String PATH = "PATH";

    /**
     * {@code Boolean} used to indicate whether the main menu entry for this action should display
     * a checkmark next to the action's text. {@code false} by default.
     */
    String CHECKMARK = "CHECKMARK";
}
