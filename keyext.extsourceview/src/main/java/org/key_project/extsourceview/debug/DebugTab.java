package org.key_project.extsourceview.debug;

import javax.annotation.Nonnull;
import javax.swing.*;
import java.awt.*;

/***
 * A single tab in the debug panel
 */
public abstract class DebugTab extends JPanel {
    public DebugTab(LayoutManager layout, boolean isDoubleBuffered) {
        super(layout, isDoubleBuffered);
    }

    public DebugTab(LayoutManager layout) {
        super(layout);
    }

    public DebugTab(boolean isDoubleBuffered) {
        super(isDoubleBuffered);
    }

    public DebugTab() {
    }

    @Nonnull
    public abstract String getTitle();
}
