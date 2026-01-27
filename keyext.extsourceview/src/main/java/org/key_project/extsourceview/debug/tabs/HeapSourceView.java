package org.key_project.extsourceview.debug.tabs;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.SequentInteractionListener;
import de.uka.ilkd.key.gui.sourceview.SourceView;
import de.uka.ilkd.key.java.NonTerminalProgramElement;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.ProgramElement;
import org.key_project.logic.Term;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.util.Pair;
import org.key_project.extsourceview.Utils;
import org.key_project.extsourceview.debug.DebugTab;
import org.key_project.extsourceview.transformer.HeapSourceCollection;

import javax.annotation.Nonnull;
import javax.swing.*;
import java.awt.*;
import java.net.URI;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Objects;

import static org.key_project.extsourceview.debug.tabs.GUIUtil.gbc;

/**
 * Class for the [Java Stmts Position] Tab in the debug panel
 *
 * Displays a bunch of information about the currently hovered term (in GoalView)
 */
public class HeapSourceView extends DebugTab {

    private JTextArea taSource;

    public HeapSourceView(@Nonnull MainWindow window, @Nonnull KeYMediator mediator) {
        super();

        initGUI(window, mediator);
    }

    private void initGUI(@Nonnull MainWindow window, @Nonnull KeYMediator mediator) {
        setLayout(new BorderLayout());

        taSource = new JTextArea();
        taSource.setEditable(false);
        taSource.setLineWrap(false);
        taSource.setFont(new Font("Courier New", Font.PLAIN, 12));

        this.add(new JScrollPane(taSource), BorderLayout.CENTER);


        var btn = new JButton("Refresh");

        btn.addActionListener(e -> calculateSources(window, mediator));

        this.add(btn, BorderLayout.NORTH);
    }

    @Nonnull
    @Override
    public String getTitle() {
        return "Heap Sources";
    }

    private void calculateSources(@Nonnull MainWindow window, @Nonnull KeYMediator mediator) {

        taSource.setText("");

        try {
            SourceView sourceView = window.getSourceViewFrame().getSourceView();

            HeapSourceCollection hsc = new HeapSourceCollection(mediator.getSelectedNode().sequent());

            hsc.collect(mediator.getSelectedNode());

            List<String> src = Files.readAllLines(Path.of(Objects.requireNonNull(sourceView.getSelectedFile())));

            StringBuilder txt = new StringBuilder();

            for (int i = 0; i < src.size(); i++) {

                int c = hsc.getHeapCount(i+1);
                if (c == 0) {
                    txt.append(String.format("[%02d] {   } %s\n", i+1, src.get(i)));
                } else {
                    txt.append(String.format("[%02d] {%03d} %s\n", i+1, c, src.get(i)));
                }

            }

            taSource.setText(txt.toString());

        } catch (Exception e) {
            taSource.setText("EXCEPTION:\n\n" + e.toString());
        }
    }
}
