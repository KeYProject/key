package de.uka.ilkd.key.gui;

import java.awt.Container;
import java.awt.Dialog;
import java.awt.Window;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JDialog;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.ScrollPaneConstants;
import javax.swing.border.TitledBorder;

/**
 * Button contained in {@link ExceptionDialog} that can be used to report an
 * error to KeY developers.
 * 
 * @author Kai Wallisch
 *
 */
public class ReportErrorButton extends JButton {
   ReportErrorButton(final Window parent, final Throwable exception) {
      super("Report Bug");
      this.setName("Report error button");
      setSelected(false);
      addActionListener(new ActionListener() {
         @Override
         public void actionPerformed(ActionEvent arg0) {
            final JDialog dialog = new JDialog(parent,
                  "Report an Error to KeY Developers",
                  Dialog.ModalityType.DOCUMENT_MODAL);
            dialog.setDefaultCloseOperation(JDialog.DISPOSE_ON_CLOSE);
            dialog.setBounds(parent.getBounds());

            JPanel right = new JPanel();
            right.setLayout(new BoxLayout(right, BoxLayout.Y_AXIS));
            right.add(new JCheckBox("Send Error Message", true));
            right.add(new JCheckBox("Send Loaded Problem", true));
            right.add(new JCheckBox("Send Stracktrace", true));
            right.add(new JCheckBox("Send KeY Version", true));

            JTextArea description = new JTextArea(20, 50);
            description.setLineWrap(true);
            description.setBorder(new TitledBorder("Error Description"));
            JScrollPane left = new JScrollPane(description);
            left.setVerticalScrollBarPolicy(ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED);
            left.setHorizontalScrollBarPolicy(ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED);

            JPanel topPanel = new JPanel();
            topPanel.setLayout(new BoxLayout(topPanel, BoxLayout.X_AXIS));
            topPanel.add(left);
            topPanel.add(right);

            JPanel buttonPanel = new JPanel();
            buttonPanel.setLayout(new BoxLayout(buttonPanel, BoxLayout.X_AXIS));
            JButton mailButton = new JButton(
                  "Create e-Mail from Error Metadata");
            JButton closeButton = new JButton("Close");
            closeButton.addActionListener(new ActionListener() {
               @Override
               public void actionPerformed(ActionEvent arg0) {
                  dialog.dispose();
               }
            });
            buttonPanel.add(mailButton);
            buttonPanel.add(closeButton);

            Container container = dialog.getContentPane();
            container.setLayout(new BoxLayout(container, BoxLayout.Y_AXIS));
            container.add(topPanel);
            container.add(buttonPanel);

            dialog.pack();
            dialog.setVisible(true);
         }
      });
   }
}
