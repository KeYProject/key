package org.key_project.keyide.ui.wizard.page;

import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.key_project.keyide.ui.util.KeYImages;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.proof.Node;

/**
 * {@link WizardPage} to edit notes of a {@link Node}.
 * @author Martin Hentschel
 */
public class EditNotesWizardPage extends WizardPage {
   /**
    * The initial notes to show.
    */
   private final String intialNodes;
   
   /**
    * Defines the notes.
    */
   private Text notesText;

   /**
    * Constructor.
    * @param pageName The name of this {@link WizardPage}.
    * @param intialNodes The initial notes to show.
    */
   public EditNotesWizardPage(String pageName, String intialNodes) {
      super(pageName);
      this.intialNodes = intialNodes;
      setDescription("Annotate the selected proof tree node.");
      setImageDescriptor(KeYImages.getImageDescriptor(KeYImages.EDIT_NOTES_WIZARD));
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void createControl(Composite parent) {
      Composite root = new Composite(parent, SWT.NONE);
      setControl(root);
      root.setLayout(new GridLayout(2, false));
      Label notesLabel = new Label(root, SWT.NONE);
      notesLabel.setText("&Notes");
      notesLabel.setLayoutData(new GridData(SWT.LEFT, SWT.TOP, false, false));
      notesText = new Text(root, SWT.BORDER | SWT.H_SCROLL | SWT.V_SCROLL | SWT.MULTI);
      SWTUtil.setText(notesText, intialNodes);
      notesText.setLayoutData(new GridData(GridData.FILL_BOTH));
   }
   
   /**
    * Returns the defined notes or {@code null} if undefined.
    * @return The defined notes or {@code null} if undefined.
    */
   public String getNotes() {
      String text = notesText.getText();
      return StringUtil.isTrimmedEmpty(text) ? null : text;
   }
}
