package org.key_project.util.eclipse.swt.dialog;

import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;

/**
 * An extended {@link MessageDialog} which allows to show an additional 
 * message in a {@link Text} control.
 * @author Martin Hentschel
 */
public class TextFieldMessageDialog extends MessageDialog {
   /**
    * The message to show in a {@link Text} control.
    */
   private final String textMessage;
   
   /**
    * Create a message dialog. Note that the dialog will have no visual
    * representation (no widgets) until it is told to open.
    * <p>
    * The labels of the buttons to appear in the button bar are supplied in
    * this constructor as an array. The <code>open</code> method will return
    * the index of the label in this array corresponding to the button that was
    * pressed to close the dialog.
    * </p>
    * <p>
    * <strong>Note:</strong> If the dialog was dismissed without pressing
    * a button (ESC key, close box, etc.) then {@link SWT#DEFAULT} is returned.
    * Note that the <code>open</code> method blocks.
    * </p>
    *
    * @param parentShell
    *            the parent shell
    * @param dialogTitle
    *            the dialog title, or <code>null</code> if none
    * @param dialogTitleImage
    *            the dialog title image, or <code>null</code> if none
    * @param dialogMessage
    *            the dialog message
    * @param dialogImageType
    *            one of the following values:
    *            <ul>
    *            <li><code>MessageDialog.NONE</code> for a dialog with no
    *            image</li>
    *            <li><code>MessageDialog.ERROR</code> for a dialog with an
    *            error image</li>
    *            <li><code>MessageDialog.INFORMATION</code> for a dialog
    *            with an information image</li>
    *            <li><code>MessageDialog.QUESTION </code> for a dialog with a
    *            question image</li>
    *            <li><code>MessageDialog.WARNING</code> for a dialog with a
    *            warning image</li>
    *            </ul>
    * @param dialogButtonLabels
    *            an array of labels for the buttons in the button bar
    * @param defaultIndex
    *            the index in the button label array of the default button
    * @param textMessage
    *            the message to show in a {@link Text} control.
    */
   public TextFieldMessageDialog(Shell parentShell, 
                                 String dialogTitle, 
                                 Image dialogTitleImage, 
                                 String dialogMessage, 
                                 int dialogImageType, 
                                 String[] dialogButtonLabels, 
                                 int defaultIndex,
                                 String textMessage) {
      super(parentShell, dialogTitle, dialogTitleImage, dialogMessage, dialogImageType, dialogButtonLabels, defaultIndex);
      this.textMessage = textMessage;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected Control createCustomArea(Composite parent) {
      if (textMessage != null) {
         Text text = new Text(parent, SWT.MULTI | SWT.BORDER | SWT.V_SCROLL | SWT.READ_ONLY);
         text.setText(textMessage);
         text.setLayoutData(new GridData(GridData.FILL_BOTH));
         return text;
      }
      else {
         return super.createCustomArea(parent);
      }
   }

   /**
    * Convenience method to open a simple dialog as specified by the
    * <code>kind</code> flag.
    * 
    * @param kind
    *            the kind of dialog to open, one of {@link #ERROR},
    *            {@link #INFORMATION}, {@link #QUESTION}, {@link #WARNING},
    *            {@link #CONFIRM}, or {@link #QUESTION_WITH_CANCEL}.
    * @param parent
    *            the parent shell of the dialog, or <code>null</code> if none
    * @param title
    *            the dialog's title, or <code>null</code> if none
    * @param message
    *            the message
    * @param style
    *            {@link SWT#NONE} for a default dialog, or {@link SWT#SHEET} for
    *            a dialog with sheet behavior
    * @param textMessage
    *            the message to show in a {@link Text} control.
    * @return <code>true</code> if the user presses the OK or Yes button,
    *         <code>false</code> otherwise
    * @since 3.5
    */
   public static boolean open(int kind, Shell parent, String title, String message, int style, String textMessage) {
      TextFieldMessageDialog dialog = new TextFieldMessageDialog(parent, title, null, message, kind, getButtonLabels(kind), 0, textMessage);
      style &= SWT.SHEET;
      dialog.setShellStyle(dialog.getShellStyle() | style);
      return dialog.open() == 0;
   }
   
   /**
    * Convenience method to open a simple confirm (OK/Cancel) dialog.
    * 
    * @param parent
    *            the parent shell of the dialog, or <code>null</code> if none
    * @param title
    *            the dialog's title, or <code>null</code> if none
    * @param message
    *            the message
    * @param textMessage
    *            the message to show in a {@link Text} control.
    * @return <code>true</code> if the user presses the OK button,
    *         <code>false</code> otherwise
    */
   public static boolean openConfirm(Shell parent, String title, String message, String textMessage) {
       return open(CONFIRM, parent, title, message, SWT.NONE, textMessage);
   }

   /**
    * Convenience method to open a standard error dialog.
    * 
    * @param parent
    *            the parent shell of the dialog, or <code>null</code> if none
    * @param title
    *            the dialog's title, or <code>null</code> if none
    * @param message
    *            the message
    * @param textMessage
    *            the message to show in a {@link Text} control.
    */
   public static void openError(Shell parent, String title, String message, String textMessage) {
       open(ERROR, parent, title, message, SWT.NONE, textMessage);
   }

   /**
    * Convenience method to open a standard information dialog.
    * 
    * @param parent
    *            the parent shell of the dialog, or <code>null</code> if none
    * @param title
    *            the dialog's title, or <code>null</code> if none
    * @param message
    *            the message
    * @param textMessage
    *            the message to show in a {@link Text} control.
    */
   public static void openInformation(Shell parent, String title, String message, String textMessage) {
       open(INFORMATION, parent, title, message, SWT.NONE, textMessage);
   }

   /**
    * Convenience method to open a simple Yes/No question dialog.
    * 
    * @param parent
    *            the parent shell of the dialog, or <code>null</code> if none
    * @param title
    *            the dialog's title, or <code>null</code> if none
    * @param message
    *            the message
    * @param textMessage
    *            the message to show in a {@link Text} control.
    * @return <code>true</code> if the user presses the Yes button,
    *         <code>false</code> otherwise
    */
   public static boolean openQuestion(Shell parent, String title, String message, String textMessage) {
       return open(QUESTION, parent, title, message, SWT.NONE, textMessage);
   }

   /**
    * Convenience method to open a standard warning dialog.
    * 
    * @param parent
    *            the parent shell of the dialog, or <code>null</code> if none
    * @param title
    *            the dialog's title, or <code>null</code> if none
    * @param message
    *            the message
    * @param textMessage
    *            the message to show in a {@link Text} control.
    */
   public static void openWarning(Shell parent, String title, String message, String textMessage) {
       open(WARNING, parent, title, message, SWT.NONE, textMessage);
   }

   /**
    * @param kind
    * @return
    */
   public static String[] getButtonLabels(int kind) {
      String[] dialogButtonLabels;
      switch (kind) {
      case ERROR:
      case INFORMATION:
      case WARNING: {
         dialogButtonLabels = new String[] { IDialogConstants.OK_LABEL };
         break;
      }
      case CONFIRM: {
         dialogButtonLabels = new String[] { IDialogConstants.OK_LABEL,
               IDialogConstants.CANCEL_LABEL };
         break;
      }
      case QUESTION: {
         dialogButtonLabels = new String[] { IDialogConstants.YES_LABEL,
               IDialogConstants.NO_LABEL };
         break;
      }
      case QUESTION_WITH_CANCEL: {
         dialogButtonLabels = new String[] { IDialogConstants.YES_LABEL,
                    IDialogConstants.NO_LABEL,
                    IDialogConstants.CANCEL_LABEL };
         break;
      }
      default: {
         throw new IllegalArgumentException(
               "Illegal value for kind in MessageDialog.open()"); //$NON-NLS-1$
      }
      }
      return dialogButtonLabels;
   }
}
