package org.key_project.extsourceview.debug.tabs;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.sourceview.SourceView;
import de.uka.ilkd.key.gui.sourceview.SourceViewInsertion;
import org.key_project.extsourceview.debug.DebugTab;

import javax.annotation.Nonnull;
import javax.swing.*;
import java.awt.*;
import java.util.stream.Collectors;

public class BackTransformationView extends DebugTab {

    public BackTransformationView(@Nonnull MainWindow window, @Nonnull KeYMediator mediator) {
        super();

        initGUI();
    }

    private void initGUI() {
        setLayout(new BorderLayout());

        add(new JLabel("TODO", JLabel.CENTER), BorderLayout.CENTER);
    }

    @Nonnull
    @Override
    public String getTitle() {
        return "Transformer";
    }
}