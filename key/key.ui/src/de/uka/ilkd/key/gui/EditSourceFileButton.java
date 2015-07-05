package de.uka.ilkd.key.gui;

import java.awt.Container;
import java.awt.Dialog;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.File;
import java.io.IOException;
import java.nio.file.Files;

import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.ScrollPaneConstants;
import javax.swing.border.TitledBorder;

import org.key_project.util.java.IOUtil;

import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.util.ExceptionTools;

/**
 * Used by {@link ExceptionDialog} to open the source file containing an error
 * for editing.
 */
public class EditSourceFileButton extends JButton {

   EditSourceFileButton(final ExceptionDialog parent, final Throwable exception) {
      super("Edit Source File");
      this.setName("Edit source file button");

      addActionListener(new ActionListener() {
         @Override
         public void actionPerformed(ActionEvent arg0) {
            try {
               Location location = ExceptionTools.getLocation(exception);
               String fileName = location.getFilename();
               if (fileName == null || fileName.length() == 0) {
                  throw new IOException(
                        "Cannot recover file location from exception.");
               }
               final File sourceFile = new File(fileName);
               String source = IOUtil.readFrom(sourceFile);
               final JDialog dialog = new JDialog(parent, "Edit "
                     + sourceFile.getName(), Dialog.ModalityType.DOCUMENT_MODAL);
               dialog.setDefaultCloseOperation(JDialog.DISPOSE_ON_CLOSE);
               dialog.setBounds(parent.getBounds());

               final JTextArea textArea = new JTextArea(30, 75);
               textArea.setText(source);
               textArea.setCaretPosition(0);
               textArea.setLineWrap(false);
               textArea.setBorder(new TitledBorder(sourceFile.getName()));
               JScrollPane top = new JScrollPane(textArea);
               top.setVerticalScrollBarPolicy(ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED);
               top.setHorizontalScrollBarPolicy(ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED);

               JPanel buttonPanel = new JPanel();
               buttonPanel.setLayout(new BoxLayout(buttonPanel,
                     BoxLayout.X_AXIS));
               JButton saveButton = new JButton("Save");
               JButton reloadButton = new JButton("Save, Close and Reload");
               JButton closeButton = new JButton("Close");
               ActionListener closeAction = new ActionListener() {
                  @Override
                  public void actionPerformed(ActionEvent arg0) {
                     dialog.dispose();
                  }
               };
               ActionListener saveAction = new ActionListener() {
                  @Override
                  public void actionPerformed(ActionEvent arg0) {
                     try {
                        Files.write(sourceFile.toPath(), textArea.getText()
                              .getBytes());
                     }
                     catch (IOException ioe) {
                        String message = "Cannot write to file:\n"
                              + ioe.getMessage();
                        JOptionPane.showMessageDialog(parent, message);
                     }
                  }
               };
               ActionListener reloadAction = new ActionListener() {
                  @Override
                  public void actionPerformed(ActionEvent arg0) {
                     parent.close();
                     MainWindow.getInstance().loadProblem(sourceFile);
                  }
               };
               closeButton.addActionListener(closeAction);
               saveButton.addActionListener(saveAction);
               reloadButton.addActionListener(saveAction);
               reloadButton.addActionListener(closeAction);
               reloadButton.addActionListener(reloadAction);
               buttonPanel.add(saveButton);
               buttonPanel.add(closeButton);
               buttonPanel.add(reloadButton);

               Container container = dialog.getContentPane();
               container.setLayout(new BoxLayout(container, BoxLayout.Y_AXIS));
               container.add(top);
               container.add(buttonPanel);

               dialog.pack();
               dialog.setVisible(true);
            }
            catch (IOException ioe) {
               String message = "Cannot open file:\n" + ioe.getMessage();
               JOptionPane.showMessageDialog(parent, message);
            }
         }
      });
   }
}
