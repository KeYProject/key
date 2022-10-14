package org.key_project.msdebug;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.sourceview.SourceView;
import de.uka.ilkd.key.gui.sourceview.SourceViewInsertion;

import javax.annotation.Nonnull;
import javax.swing.*;
import java.awt.*;

public class SourceInsertionsView extends MSDebugTab {

    private final SourceView sourceView;

    public SourceInsertionsView(@Nonnull MainWindow window, @Nonnull KeYMediator mediator) {
        super();

        sourceView = window.getSourceViewFrame().getSourceView();

        initGUI();
    }

    private void initGUI() {
        setLayout(new GridLayout(3, 1, 8, 8));

        JTextField ed1 = new JTextField("3");
        JTextField ed2 = new JTextField("Some Text");
        JButton btn1 = new JButton("Add Insertion");
        btn1.addActionListener((e) -> addInsertion(ed1.getText(), ed2.getText()));
        add(ed1);
        add(ed2);
        add(btn1);
    }

    private void addInsertion(String pos, String text) {
        try {

            int intpos = Integer.parseInt(pos);

            SourceViewInsertion ins = new SourceViewInsertion("debug", intpos, text, Color.BLACK, Color.LIGHT_GRAY);

            sourceView.addInsertion(sourceView.getSelectedFile(), ins);

        } catch (Exception e) {
            JOptionPane.showMessageDialog(SourceInsertionsView.this, e.toString());
        }
    }

    @Nonnull
    @Override
    public String getTitle() {
        return "Source Insertions";
    }
}