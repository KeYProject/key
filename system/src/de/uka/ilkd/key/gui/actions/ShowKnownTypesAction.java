package de.uka.ilkd.key.gui.actions;

import java.awt.BorderLayout;
import java.awt.Container;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyEvent;

import javax.swing.BorderFactory;
import javax.swing.JButton;
import javax.swing.JComponent;
import javax.swing.JDialog;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.KeyStroke;
import javax.swing.WindowConstants;

import de.uka.ilkd.key.gui.ClassTree;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.notification.events.GeneralInformationEvent;
import de.uka.ilkd.key.proof.Proof;

public class ShowKnownTypesAction extends MainWindowAction {

    /**
     * 
     */
    private static final long serialVersionUID = 4368162229726580799L;

    public ShowKnownTypesAction(MainWindow mainWindow) {
	super(mainWindow);
	setName("Show Known Types...");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
	showTypeHierarchy();
    }
    
    private void showTypeHierarchy() {
        Proof currentProof = getMediator().getProof();
        if(currentProof == null) {
            getMediator().notify(new GeneralInformationEvent("No Type Hierarchy available.",
                    "If you wish to see the types "
                    + "for a proof you have to load one first"));
        } else {
            final JDialog dialog = new JDialog(mainWindow, "Known types for this proof", true);
            dialog.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
            Container pane = dialog.getContentPane();
            pane.setLayout(new BorderLayout());
            {   
                JScrollPane scrollpane = new JScrollPane();
                ClassTree classTree = new ClassTree(false, false, currentProof.getServices());
                classTree.setBorder(BorderFactory.createEmptyBorder(5, 5, 5, 5));
                scrollpane.setViewportView(classTree);
                pane.add(scrollpane, BorderLayout.CENTER);
            }
            {
                final JButton button = new JButton("OK");
                button.addActionListener(new ActionListener() {
                    public void actionPerformed(ActionEvent e) {
                        dialog.setVisible(false);
                        dialog.dispose();
                    }
                });
                {
                    JPanel panel = new JPanel();
                    panel.add(button);
                    pane.add(panel, BorderLayout.SOUTH);
                    dialog.getRootPane().setDefaultButton(button);
                    ActionListener escapeListener = new ActionListener() {
                	public void actionPerformed(ActionEvent event) {
                	    if(event.getActionCommand().equals("ESC")) {
                		button.doClick();
                	    }
                	}
                    };
                    button.registerKeyboardAction(
                	    escapeListener,
                	    "ESC",
                	    KeyStroke.getKeyStroke(KeyEvent.VK_ESCAPE, 0),
                	    JComponent.WHEN_IN_FOCUSED_WINDOW);

                }
            }
            dialog.setSize(300, 400);
            dialog.setLocationRelativeTo(mainWindow);
            dialog.setVisible(true);
        }
    }

}
