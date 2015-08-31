package de.uka.ilkd.key.gui.actions;

import java.awt.BorderLayout;
import java.awt.Container;
import java.awt.Dialog;
import java.awt.FlowLayout;
import java.awt.Rectangle;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.File;
import java.io.IOException;
import java.nio.file.Files;

import javax.swing.AbstractAction;
import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JSplitPane;
import javax.swing.JTextArea;
import javax.swing.ScrollPaneConstants;
import javax.swing.border.TitledBorder;

import org.key_project.util.java.IOUtil;

import de.uka.ilkd.key.gui.ExceptionDialog;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.util.ExceptionTools;

/**
 * Used by {@link ExceptionDialog} to open the source file containing an error
 * for editing.
 *
 * @author Kai Wallisch
 */
public class EditSourceFileAction extends AbstractAction {

   /**
    * Moves the caret in a {@link JTextArea} to the specified position. Assumes
    * the first position in the textarea is in line 1 column 1.
    */
   private static void textAreaGoto(JTextArea textArea, int line, int col) {
      String text = textArea.getText();
      int i = 0;
      while (i < text.length() && line > 1) {
         if (text.charAt(i) == '\n') {
            line--;
         }
         i++;
      }
      i += col - 1;
      textArea.setCaretPosition(i);
   }

   private final ExceptionDialog parent;
   private final Throwable exception;
   
   public EditSourceFileAction(final ExceptionDialog parent, final Throwable exception) {
      super("Edit Source File");
      this.parent = parent;
      this.exception = exception;
   }
   
   public boolean isValidLocation(final Location location) {
       return !(location == null || location.getFilename() == null
              || location.getFilename().length() == 0);
   }

   @Override
   public void actionPerformed(ActionEvent arg0) {
      try {
         final Location location = ExceptionTools.getLocation(exception);
         if (!isValidLocation(location)) {
            throw new IOException("Cannot recover file location from exception.");
         }

         String fileName = location.getFilename();
         final File sourceFile = new File(fileName);
         String source = IOUtil.readFrom(sourceFile);

         final JDialog dialog = new JDialog(parent, "Edit "
               + sourceFile.getName(), Dialog.ModalityType.DOCUMENT_MODAL);
         dialog.setDefaultCloseOperation(JDialog.DISPOSE_ON_CLOSE);

         int columnNumber = 75;

         JTextArea parserMessage = new JTextArea();
         String message = exception.getMessage();
         parserMessage.setText(message);
         parserMessage.setEditable(false);
         parserMessage.setColumns(columnNumber);
         // approximate # rows
         parserMessage.setRows(message.length() / (columnNumber-10));
         parserMessage.setLineWrap(true);
         parserMessage.setWrapStyleWord(true);
         parserMessage.setBorder(new TitledBorder("Parser Message"));
         JScrollPane parserMessageScrollPane = new JScrollPane(parserMessage);
         parserMessageScrollPane
               .setVerticalScrollBarPolicy(ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED);
         parserMessageScrollPane
               .setHorizontalScrollBarPolicy(ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED);

         final JTextArea textArea = new JTextArea(30, columnNumber) {
            @Override
            public void addNotify() {
               super.addNotify();
               requestFocus();
               textAreaGoto(this, location.getLine(), location.getColumn());
            }
         };
         textArea.setText(source);
         textArea.setFont(ExceptionDialog.MESSAGE_FONT);
         textArea.setLineWrap(false);
         textArea.setBorder(new TitledBorder(sourceFile.getName()));
         JScrollPane textAreaScrollPane = new JScrollPane(textArea);
         textAreaScrollPane
               .setVerticalScrollBarPolicy(ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED);
         textAreaScrollPane
               .setHorizontalScrollBarPolicy(ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED);

         JPanel buttonPanel = new JPanel();
         buttonPanel.setLayout(new FlowLayout());
         JButton saveButton = new JButton("Save");
         JButton reloadButton = new JButton("Save, Close and Reload");
         JButton cancelButton = new JButton("Cancel");
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
                  String message = "Cannot write to file:\n" + ioe.getMessage();
                  JOptionPane.showMessageDialog(parent, message);
               }
            }
         };
         ActionListener reloadAction = new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent arg0) {
               parent.setVisible(false);
               MainWindow.getInstance().loadProblem(sourceFile);
            }
         };
         cancelButton.addActionListener(closeAction);
         saveButton.addActionListener(saveAction);
         reloadButton.addActionListener(saveAction);
         reloadButton.addActionListener(closeAction);
         reloadButton.addActionListener(reloadAction);
         buttonPanel.add(saveButton);
         buttonPanel.add(cancelButton);
         buttonPanel.add(reloadButton);

         Container container = dialog.getContentPane();
         //container.setLayout(new BoxLayout(container, BoxLayout.Y_AXIS));
         JSplitPane splitPane = new JSplitPane(JSplitPane.VERTICAL_SPLIT);
         splitPane.setTopComponent(parserMessageScrollPane);
         splitPane.setBottomComponent(textAreaScrollPane);
         container.add(splitPane, BorderLayout.CENTER);
         container.add(buttonPanel, BorderLayout.SOUTH);

         dialog.pack();
         centerDialogRelativeToMainWindow(dialog);
         dialog.setVisible(true);
      }
      catch (IOException ioe) {
         String message = "Cannot open file:\n" + ioe.getMessage();
         JOptionPane.showMessageDialog(parent, message);
      }
   }

   static void centerDialogRelativeToMainWindow(final JDialog dialog) {
       dialog.setLocationRelativeTo(MainWindow.getInstance());
//      Rectangle bounds = dialog.getBounds();
//      Rectangle mainWindowBounds = MainWindow.getInstance().getBounds();
//      int x = Math.max(0, mainWindowBounds.x
//            + (mainWindowBounds.width - bounds.width) / 2);
//      int y = Math.max(0, mainWindowBounds.y
//            + (mainWindowBounds.height - bounds.height) / 2);
//      dialog.setBounds(x, y, bounds.width, bounds.height);
   }
}
