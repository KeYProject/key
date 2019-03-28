package de.uka.ilkd.key.gui.ext;

import javax.swing.*;
import java.util.Iterator;

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

}
