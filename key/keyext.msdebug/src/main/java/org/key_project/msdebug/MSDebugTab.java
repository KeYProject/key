package org.key_project.msdebug;

import javax.annotation.Nonnull;
import javax.swing.*;
import java.awt.*;

public abstract class MSDebugTab extends JPanel {
    public MSDebugTab(LayoutManager layout, boolean isDoubleBuffered) {
        super(layout, isDoubleBuffered);
    }

    public MSDebugTab(LayoutManager layout) {
        super(layout);
    }

    public MSDebugTab(boolean isDoubleBuffered) {
        super(isDoubleBuffered);
    }

    public MSDebugTab() {
    }

    @Nonnull public abstract String getTitle();
}
