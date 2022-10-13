package org.key_project.msdebug;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.SequentInteractionListener;
import de.uka.ilkd.key.gui.sourceview.SourceView;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermImpl;
import de.uka.ilkd.key.logic.origin.OriginRef;
import de.uka.ilkd.key.pp.PosInSequent;

import javax.annotation.Nonnull;
import javax.swing.*;
import javax.swing.text.BadLocationException;
import java.awt.*;
import java.io.IOException;
import java.net.URISyntaxException;
import java.util.ArrayList;

public class SourceInsertionsView extends MSDebugTab {

    private final SourceView sourceView;

    public SourceInsertionsView(@Nonnull MainWindow window, @Nonnull KeYMediator mediator) {
        super();

        sourceView = window.getSourceViewFrame().getSourceView();

        initGUI();
    }

    private void initGUI() {
        setLayout(new GridLayout(1, 2, 20, 20));

        JTextField ed1 = new JTextField("3");
        JButton btn1 = new JButton("Add Insertion");
        btn1.addActionListener((e) -> addInsertion(ed1.getText()));
        add(ed1);
        add(btn1);
    }

    private void addInsertion(String pos) {
        try {

            int intpos = Integer.parseInt(pos);

            //do something

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