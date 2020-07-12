// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui.nodeviews;

import java.awt.*;
import java.awt.event.KeyEvent;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;

import javax.swing.*;
import javax.swing.border.EmptyBorder;
import javax.swing.event.AncestorEvent;
import javax.swing.event.AncestorListener;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.CopyToClipboardAction;
import de.uka.ilkd.key.gui.prooftree.ProofTreeView;

/**
 * Central part of MainWindow. Its main purpose is to serve as container for
 * SequentView instances.
 *
 * @author Kai Wallisch
 */
public final class MainFrame extends JPanel {

    private static final long serialVersionUID = -2412537422601138379L;

    private final MainWindow mainWindow;
    private final JScrollPane scrollPane = new JScrollPane();
    private Component content;

    public Component setContent(Component component) {
        Component oldContent = content;
        content = component;
        if (component instanceof SequentView) {
            SequentView sequentView = (SequentView) component;
            Point oldSequentViewPosition = scrollPane.getViewport().getViewPosition();
            scrollPane.setViewportView(new SequentViewPanel(sequentView));
            scrollPane.getViewport().setViewPosition(oldSequentViewPosition);

            // Additional option to show taclet info in case of:
            // sequentView instanceof InnerNodeView
            ProofTreeView ptv = mainWindow.getProofTreeView();
            if (ptv != null) {
                ptv.tacletInfoToggle.setSequentView(sequentView);
            }
        } else {
            scrollPane.setViewportView(component);
        }

        if (oldContent instanceof SequentView) {
            ((SequentView) oldContent).removeUserSelectionHighlight();
        }

        return oldContent;
    }

    public MainFrame(final MainWindow mainWindow, EmptySequent emptySequent) {
        this.mainWindow = mainWindow;
        setBorder(new EmptyBorder(0, 0, 0, 0));
        scrollPane.getVerticalScrollBar().setUnitIncrement(30);
        scrollPane.getHorizontalScrollBar().setUnitIncrement(30);

        addMouseListener(new MouseAdapter() {

            @Override
            public void mouseClicked(MouseEvent e) {
                if (content != null) {
                    for (MouseListener listener : content.getMouseListeners()) {
                        if (listener instanceof SequentViewInputListener) {
                            listener.mouseClicked(e);
                        }
                    }
                }
            }
        });

        addAncestorListener(new AncestorListener() {

            @Override
            public void ancestorRemoved(AncestorEvent event) {
                if (content instanceof SequentView) {
                    ((SequentView) content).removeUserSelectionHighlight();
                }
            }

            @Override
            public void ancestorMoved(AncestorEvent event) { }

            @Override
            public void ancestorAdded(AncestorEvent event) { }
        });

        // FIXME put this somewhere descent
        getInputMap(JComponent.WHEN_IN_FOCUSED_WINDOW).put(
                KeyStroke.getKeyStroke(
                        KeyEvent.VK_C,
                        Toolkit.getDefaultToolkit().getMenuShortcutKeyMask()),
                        "copy");
        getActionMap().put("copy", new CopyToClipboardAction(mainWindow));
        setLayout(new BorderLayout());
        add(scrollPane);
        setContent(emptySequent);
    }
}