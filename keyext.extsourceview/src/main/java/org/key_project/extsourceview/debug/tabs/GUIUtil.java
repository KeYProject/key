package org.key_project.extsourceview.debug.tabs;

import java.awt.*;

/**
 * A few useful utils to create GUIs
 */
public class GUIUtil {
    public static GridBagConstraints gbc(int x, int y) {
        return new GridBagConstraints(x, y, 1, 1, 1.0, 1.0, GridBagConstraints.CENTER,
            GridBagConstraints.BOTH, new Insets(0, 0, 0, 0), 0, 0);
    }

    public static GridBagConstraints gbc(int x, int y, int sx, int sy) {
        return new GridBagConstraints(x, y, sx, sy, 1.0, 1.0, GridBagConstraints.CENTER,
            GridBagConstraints.BOTH, new Insets(2, 2, 2, 2), 0, 0);
    }

    public static GridBagConstraints gbcf(int x, int y) {
        return new GridBagConstraints(x, y, 1, 1, 0.0, 0.0, GridBagConstraints.CENTER,
                GridBagConstraints.BOTH, new Insets(2, 6, 2, 6), 0, 0);
    }

    public static GridBagConstraints gbcf(int x, int y, int sx, int sy) {
        return new GridBagConstraints(x, y, sx, sy, 0.0, 0.0, GridBagConstraints.CENTER,
                GridBagConstraints.BOTH, new Insets(2, 6, 2, 6), 0, 0);
    }
}
