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

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.CopyToClipboardAction;
import de.uka.ilkd.key.gui.prooftree.ProofTreeView;
import java.awt.Component;
import java.awt.Point;
import java.awt.Toolkit;
import java.awt.event.KeyEvent;
import javax.swing.JComponent;
import javax.swing.JScrollPane;
import javax.swing.KeyStroke;
import javax.swing.border.EmptyBorder;

/**
 * Central part of MainWindow. Its main purpose is to serve as container for
 * SequentView instances.
 *
 * @author Kai Wallisch
 */
public final class MainFrame extends JScrollPane {

    private static final long serialVersionUID = 513236416130998762L;

    private final MainWindow mainWindow;

    private Component content;

    public Component setContent(Component component) {
        Component oldContent = content;
        content = component;
        if (component instanceof SequentView) {
            SequentView sequentView = (SequentView) component;
            Point oldSequentViewPosition = getViewport().getViewPosition();
            setViewportView(new SequentViewPanel(sequentView));
            getViewport().setViewPosition(oldSequentViewPosition);

            // Additional option to show taclet info in case of: sequentView instanceof InnerNodeView
            ProofTreeView ptv = mainWindow.getProofTreeView();
            if (ptv != null) {
                ptv.tacletInfoToggle.setSequentView(sequentView);
            }
        } else {
            setViewportView(component);
        }
        return oldContent;
    }

    public MainFrame(final MainWindow mainWindow, EmptySequent emptySequent) {
        this.mainWindow = mainWindow;
        setBorder(new EmptyBorder(0, 0, 0, 0));
        getVerticalScrollBar().setUnitIncrement(30);
        getHorizontalScrollBar().setUnitIncrement(30);

        // FIXME put this somewhere descent
        getInputMap(JComponent.WHEN_IN_FOCUSED_WINDOW).put(
                KeyStroke.getKeyStroke(KeyEvent.VK_C, Toolkit.getDefaultToolkit().getMenuShortcutKeyMask()),
                "copy");
        getActionMap().put("copy", new CopyToClipboardAction(mainWindow));
        setContent(emptySequent);
    }
}