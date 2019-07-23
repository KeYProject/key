package org.key_project.exploration;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.fonticons.*;

import java.awt.*;

/**
 * @author Alexander Weigl
 * @version 1 (22.07.19)
 */
public class Icons {
    public final static IconFontProvider WARNING =
            new IconFontProvider(MaterialDesignRegular.WARNING, Color.yellow);

    public final static IconFontProvider EXPLORE =
            new IconFontProvider(MaterialDesignRegular.EXPLORE);

    public static final IconProvider SECOND_BRANCH = new IconFontProvider(
            FontAwesomeSolid.BALANCE_SCALE);
}
