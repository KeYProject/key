package org.key_project.exploration;

import de.uka.ilkd.key.gui.fonticons.*;

import javax.swing.*;
import java.awt.*;

/**
 * @author Alexander Weigl
 * @version 1 (22.07.19)
 */
public class Icons {
    public final static IconFontProvider WARNING =
            new IconFontProvider(MaterialDesignRegular.WARNING, Color.yellow);

    public static final Image SECOND_BRANCH_IMAGE = IconFontSwing.buildImage(FontAwesomeSolid.SHARE_ALT, 18, Color.BLACK, 90.0);

    public final static IconFontProvider EXPLORE =
            new IconFontProvider(MaterialDesignRegular.EXPLORE);

    public static final Icon SECOND_BRANCH = new ImageIcon(SECOND_BRANCH_IMAGE);
            //= new IconFontProvider(FontAwesomeSolid.SHARE_ALT);

    public static final IconProvider SECOND_BRANCH_HIDE = new IconFontProvider(
            FontAwesomeSolid.ELLIPSIS_V);
}
