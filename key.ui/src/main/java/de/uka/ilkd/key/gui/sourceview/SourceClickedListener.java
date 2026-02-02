package de.uka.ilkd.key.gui.sourceview;

import org.jspecify.annotations.Nullable;

import java.awt.event.MouseEvent;
import java.util.EventListener;

public interface SourceClickedListener extends EventListener {
    void sourceClicked(@Nullable SourceViewInsertion insertion, MouseEvent e);
}
