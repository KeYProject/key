package org.key_project.extsourceview.debug.tabs;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.sourceview.SourceView;
import org.key_project.extsourceview.debug.DebugTab;

import javax.annotation.Nonnull;
import javax.swing.*;
import java.awt.*;
import java.util.stream.Collectors;

public class SourceHighlightsView extends DebugTab {

    private final SourceView sourceView;

    public SourceHighlightsView(@Nonnull MainWindow window, @Nonnull KeYMediator mediator) {
        super();

        sourceView = window.getSourceViewFrame().getSourceView();

        initGUI(sourceView);
    }

    private void initGUI(SourceView sv) {
        setLayout(new BorderLayout());

        var dlm = new DefaultListModel<String>();
        var list = new JList<>(dlm);

        Runnable refresh = () -> {
            try {
                var data = this.sourceView.listHighlights(this.sourceView.getSelectedFile()).
                        stream().
                        map(p -> String.format("[%s] [+%d] {%d -> %d} (%s)", p.getGroup(), p.getLevel(), p.getSourceLine(), p.getPatchedLine(), colHex(p.getColor()))).
                        collect(Collectors.toList());
                dlm.clear();
                dlm.addAll(data);
            } catch (Exception ex) {
                dlm.clear();
                dlm.addElement(ex.toString());
            }
        };

        list.setFont(Font.getFont("Courier New"));

        sv.addHighlightsChangedListener(refresh::run);

        add(new JScrollPane(list), BorderLayout.CENTER);
    }

    private String colHex(Color color) {
        return String.format("#%02X%02X%02X", color.getRed(), color.getGreen(), color.getBlue());
    }

    private static GridBagConstraints gbc(int x, int y) {
        return new GridBagConstraints
                (
                        x, y,
                        1, 1,
                        1.0 , 1.0,
                        GridBagConstraints.CENTER,
                        GridBagConstraints.BOTH,
                        new Insets(2, 2, 2, 2),
                        0, 0
                );
    }

    private static GridBagConstraints gbc(int x, int y,int sx, int sy) {
        return new GridBagConstraints
                (
                        x, y,
                        sx, sy,
                        1.0 , 1.0,
                        GridBagConstraints.CENTER,
                        GridBagConstraints.BOTH,
                        new Insets(2, 2, 2, 2),
                        0, 0
                );
    }

    @Nonnull
    @Override
    public String getTitle() {
        return "Source Higlights";
    }
}