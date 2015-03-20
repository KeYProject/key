package org.key_project.jmlediting.ui.preferencepages.profileDialog;

import org.eclipse.jface.dialogs.IMessageProvider;
import org.eclipse.jface.dialogs.TitleAreaDialog;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;
import org.key_project.jmlediting.core.profile.IEditableDerivedProfile;
import org.key_project.jmlediting.core.profile.syntax.IKeywordSort;
import org.key_project.jmlediting.core.profile.syntax.user.IUserDefinedKeywordContentDescription;

public class JMLKeywordDialog extends TitleAreaDialog {
   private final IEditableDerivedProfile derivedProfile;

   private Text keywordText;
   private Combo contentCombo;
   private Combo endingCharacterCombo;
   private Combo sortCombo;
   private Text descriptionText;

   public JMLKeywordDialog(final Shell parent,
         final IEditableDerivedProfile derivedProfile) {
      super(parent);
      this.derivedProfile = derivedProfile;
      this.setHelpAvailable(false);
   }

   @Override
   public void create() {
      super.create();
      this.setTitle("Dummy Title");
      this.setMessage("Only a Dummy", IMessageProvider.WARNING);
   }

   @Override
   protected Control createDialogArea(final Composite parent) {
      final Composite composite = (Composite) super.createDialogArea(parent);
      final GridData data = new GridData(SWT.FILL, SWT.FILL, true, true);
      final Composite myComposite = new Composite(composite, SWT.NONE);
      myComposite.setLayoutData(data);
      myComposite.setLayout(new GridLayout(3, false));

      this.addLabel(myComposite, "Keyword:", 1, 0, 0);

      this.addLabel(myComposite, "Content:", 1, 20, 0);

      this.addLabel(myComposite, "", 1, 20, 0);

      this.addKeywordText(myComposite);

      this.addContentCombo(myComposite);

      this.addEndingCharacterCombo(myComposite);

      this.addLabel(myComposite, "Keyword Sort:", 3, 0, 20);

      this.addSortCombo(myComposite);

      this.addLabel(myComposite, "Description:", 3, 0, 20);

      this.addDescriptionText(myComposite);

      this.fillCombos();

      return composite;
   }

   private void fillCombos() {
      for (final IUserDefinedKeywordContentDescription content : this.derivedProfile
            .getSupportedContentDescriptions()) {
         this.contentCombo.add(content.getDescription());
         System.out.println("added: \"" + content.getDescription() + "\"");
         this.contentCombo.setData(content.getDescription(), content);
      }

      for (final IKeywordSort sort : this.derivedProfile
            .getAvailableKeywordSorts()) {
         this.sortCombo.add(sort.getDescription());
         this.sortCombo.setData(sort.getDescription(), sort);
      }

      this.endingCharacterCombo.add("");
      this.endingCharacterCombo.add(";");
      this.endingCharacterCombo.select(0);
   }

   private void addDescriptionText(final Composite myComposite) {
      final GridData data = new GridData(SWT.FILL, SWT.TOP, true, true, 3, 1);
      data.heightHint = 100;
      this.descriptionText = new Text(myComposite, SWT.MULTI | SWT.BORDER
            | SWT.V_SCROLL | SWT.WRAP);
      this.descriptionText.setLayoutData(data);
   }

   private void addEndingCharacterCombo(final Composite myComposite) {
      final GridData data = new GridData(SWT.LEFT, SWT.TOP, false, false, 1, 1);
      data.horizontalIndent = 20;
      this.endingCharacterCombo = new Combo(myComposite, SWT.BORDER
            | SWT.READ_ONLY);
      this.endingCharacterCombo.setLayoutData(data);
   }

   private void addSortCombo(final Composite myComposite) {
      final GridData data = new GridData(SWT.LEFT, SWT.TOP, false, false, 3, 1);
      this.sortCombo = new Combo(myComposite, SWT.BORDER | SWT.READ_ONLY);
      this.sortCombo.setLayoutData(data);
   }

   private void addContentCombo(final Composite myComposite) {
      final GridData data = new GridData(SWT.LEFT, SWT.TOP, false, false, 1, 1);
      data.horizontalIndent = 20;
      this.contentCombo = new Combo(myComposite, SWT.BORDER | SWT.READ_ONLY);
      this.contentCombo.setLayoutData(data);
   }

   private void addLabel(final Composite myComposite, final String text,
         final int horizontalSpan, final int horizontalIntent,
         final int verticalIntent) {
      final GridData data = new GridData(SWT.LEFT, SWT.TOP, false, false,
            horizontalSpan, 1);
      data.verticalIndent = verticalIntent;
      data.horizontalIndent = horizontalIntent;
      final Label label = new Label(myComposite, SWT.NONE);
      label.setText(text);
      label.setLayoutData(data);
   }

   private void addKeywordText(final Composite myComposite) {
      final GridData data = new GridData(SWT.FILL, SWT.TOP, false, true);
      data.widthHint = 175;
      this.keywordText = new Text(myComposite, SWT.SINGLE | SWT.BORDER);
      this.keywordText.setLayoutData(data);
   }

   @Override
   protected void okPressed() {
      super.okPressed();
   }
}
