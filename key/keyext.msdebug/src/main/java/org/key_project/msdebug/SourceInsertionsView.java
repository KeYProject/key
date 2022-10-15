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
        setLayout(new GridLayout(4, 1, 8, 8));

        JTextField ed1 = new JTextField("3");
        JTextField ed2 = new JTextField("    "+"    "+"Some Text");
        JButton btn1 = new JButton("Add Insertion");
        btn1.addActionListener((e) -> addInsertion(ed1.getText(), ed2.getText()));
        JButton btn2 = new JButton("Clear Insertion");
        btn2.addActionListener((e) -> clearInsertions());
        add(ed1);
        add(ed2);
        add(btn1);
        add(btn2);
    }

    private void clearInsertions() {
        try {

            sourceView.clearInsertion(sourceView.getSelectedFile(), "debug");

        } catch (Exception e) {
            JOptionPane.showMessageDialog(SourceInsertionsView.this, e.toString());
        }
    }

    private void addInsertion(String pos, String text) {
        try {
            int intpos = Integer.parseInt(pos);

            SourceViewInsertion ins = new SourceViewInsertion("debug", intpos, text, Color.BLACK, new Color(222, 222, 222));

            ins.addClickListener(e ->      JOptionPane.showMessageDialog(null, "[LeftClick]\n"  + text));
            ins.addRightClickListener(e -> JOptionPane.showMessageDialog(null, "[RightClick]\n" + text));

            ins.addMouseEnterListener(e -> System.out.println("[ENTER] " + text));
            ins.addMouseMoveListener(e ->  System.out.println("[MOVE]  " + text));
            ins.addMouseLeaveListener(e -> System.out.println("[LEAVE] " + text));

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