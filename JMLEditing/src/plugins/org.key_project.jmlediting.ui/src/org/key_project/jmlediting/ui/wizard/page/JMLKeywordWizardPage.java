package org.key_project.jmlediting.ui.wizard.page;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import org.eclipse.jface.fieldassist.ControlDecoration;
import org.eclipse.jface.fieldassist.FieldDecorationRegistry;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.key_project.jmlediting.core.profile.IEditableDerivedProfile;
import org.key_project.jmlediting.core.profile.syntax.IKeywordSort;
import org.key_project.jmlediting.core.profile.syntax.user.IUserDefinedKeyword;
import org.key_project.jmlediting.core.profile.syntax.user.IUserDefinedKeywordContentDescription;
import org.key_project.jmlediting.core.profile.syntax.user.UserDefinedKeyword;
import org.key_project.jmlediting.ui.util.JMLEditingImages;
import org.key_project.jmlediting.ui.wizard.JMLKeywordWizard;
import org.key_project.util.java.StringUtil;

/**
 * The {@link WizardPage} to edit {@link IUserDefinedKeyword}s.
 * @author Martin Hentschel
 * @see JMLKeywordWizard
 */
public class JMLKeywordWizardPage extends WizardPage {
   public static final String CLOSING_CHARACTER_ID = "ClosingCharacter";
   
   /**
    * the Profile to define the keyword for.
    */
   private final IEditableDerivedProfile derivedProfile;

   /**
    * the selected keyword to edit (null when new keyword).
    */
   private final IUserDefinedKeyword keyword;

   /**
    * the Widget containing the Keyword itself.
    */
   private Text keywordText;

   /**
    * the Widget containing the available ContentDescriptions.
    */
   private Combo contentCombo;

   /**
    * the Widget containing the available closing characters.
    */
   private Combo closingCharacterCombo;

   /**
    * the Widget containing the available keyword sorts.
    */
   private Combo sortCombo;

   /**
    * the Widget containing the keyword description.
    */
   private Text descriptionText;

   /**
    * the Widget to display keyword validation Error.
    */
   private ControlDecoration keywordTextError;

   public JMLKeywordWizardPage(String pageName, final IEditableDerivedProfile derivedProfile, final IUserDefinedKeyword keyword) {
      super(pageName);
      this.derivedProfile = derivedProfile;
      this.keyword = keyword;
      setImageDescriptor(JMLEditingImages.getImageDescriptor(JMLEditingImages.JML_WIZARD));
      if (this.keyword != null) {
         this.setTitle("Edit Keyword");
         setDescription("Edit the content of the existing keyword.");
      }
      else {
         this.setTitle("Create New Keyword");
         setDescription("Define the content of the new keyword.");
      }
   }

   @Override
   public void createControl(Composite parent) {
      final Composite myComposite = new Composite(parent, SWT.NONE);
      setControl(parent);
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

      if (this.keyword != null) {
         this.fillView();
      }
   }
   
   /**
    * fill the view to edit the given keyword.
    */
   private void fillView() {
      String formattedKeyword = "";
      final Iterator<String> iterator = this.keyword.getKeywords().iterator();
      while (iterator.hasNext()) {
         formattedKeyword += iterator.next();
         if (iterator.hasNext()) {
            formattedKeyword += ", ";
         }
      }
      this.keywordText.setText(formattedKeyword);

      for (int i = 0; i < this.contentCombo.getItemCount(); i++) {
         final IUserDefinedKeywordContentDescription content = (IUserDefinedKeywordContentDescription) this.contentCombo
               .getData(this.contentCombo.getItem(i));
         if (content.getId().equals(
               this.keyword.getContentDescription().getId())) {
            this.contentCombo.select(i);
            break;
         }
      }

      if (this.keyword.getClosingCharacter() == null) {
         this.closingCharacterCombo.select(0);
      }
      else {
         for (int i = 1; i < this.closingCharacterCombo.getItemCount(); i++) {
            final Character endingChar = this.closingCharacterCombo.getItem(i)
                  .charAt(0);
            if (endingChar.equals(this.keyword.getClosingCharacter())) {
               this.closingCharacterCombo.select(i);
               break;
            }
         }
      }

      for (int i = 0; i < this.sortCombo.getItemCount(); i++) {
         final IKeywordSort sort = (IKeywordSort) this.sortCombo
               .getData(this.sortCombo.getItem(i));
         if (sort.getDescription().equals(
               this.keyword.getSort().getDescription())) {
            this.sortCombo.select(i);
            break;
         }
      }

      this.descriptionText.setText(this.keyword.getDescription());
   }

   /**
    * fill the comboboxes with the available values and select by default the
    * first item.
    */
   private void fillCombos() {
      final List<IUserDefinedKeywordContentDescription> descriptions = new ArrayList<IUserDefinedKeywordContentDescription>(
            this.derivedProfile.getSupportedContentDescriptions());
      Collections.sort(descriptions,
            new Comparator<IUserDefinedKeywordContentDescription>() {
               @Override
               public int compare(
                     final IUserDefinedKeywordContentDescription o1,
                     final IUserDefinedKeywordContentDescription o2) {
                  return o1.getDescription().compareTo(o2.getDescription());
               }
            });
      for (final IUserDefinedKeywordContentDescription content : descriptions) {
         this.contentCombo.add(content.getDescription());
         this.contentCombo.setData(content.getDescription(), content);
      }
      this.contentCombo.select(0);

      final List<IKeywordSort> sorts = new ArrayList<IKeywordSort>(
            this.derivedProfile.getAvailableKeywordSorts());
      Collections.sort(sorts, new Comparator<IKeywordSort>() {
         @Override
         public int compare(final IKeywordSort o1, final IKeywordSort o2) {
            return o1.getDescription().compareTo(o2.getDescription());
         }
      });
      for (final IKeywordSort sort : sorts) {
         this.sortCombo.add(sort.getDescription());
         this.sortCombo.setData(sort.getDescription(), sort);
         if (sort.getDescription().equals("Toplevel Keyword")) {
            this.sortCombo.select(this.sortCombo.getItemCount() - 1);
         }
      }

      this.closingCharacterCombo.add("");
      this.closingCharacterCombo.add(";");
      this.closingCharacterCombo.select(0);
      
      updatePageCompleted();
   }

   private void addDescriptionText(final Composite myComposite) {
      final GridData data = new GridData(GridData.FILL_BOTH);
      data.horizontalSpan = 3;
      data.heightHint = 200;
      this.descriptionText = new Text(myComposite, SWT.MULTI | SWT.BORDER | SWT.V_SCROLL | SWT.WRAP);
      this.descriptionText.setLayoutData(data);
   }

   private void addEndingCharacterCombo(final Composite myComposite) {
      final GridData data = new GridData(SWT.LEFT, SWT.TOP, false, false, 1, 1);
      data.horizontalIndent = 20;
      this.closingCharacterCombo = new Combo(myComposite, SWT.BORDER
            | SWT.READ_ONLY);
      this.closingCharacterCombo.setLayoutData(data);
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

      this.keywordTextError = new ControlDecoration(this.keywordText, SWT.RIGHT
            | SWT.TOP);
      this.keywordTextError.setImage(FieldDecorationRegistry.getDefault()
            .getFieldDecoration(FieldDecorationRegistry.DEC_ERROR).getImage());
      this.keywordTextError.setDescriptionText("Keyword must not be empty!");
      this.keywordTextError.show();

      this.keywordText.addModifyListener(new ModifyListener() {
         @Override
         public void modifyText(final ModifyEvent e) {
            updatePageCompleted();
            
         }
      });
   }

   protected void updatePageCompleted() {
      String errorMessage = null;
      // Validate text
      if (!computeKeywords().isEmpty()) {
         JMLKeywordWizardPage.this.keywordTextError.hide();
      }
      else {
         JMLKeywordWizardPage.this.keywordTextError.show();
         errorMessage = keywordTextError.getDescriptionText();
      }
      // Update page completed
      setPageComplete(errorMessage == null);
      setErrorMessage(errorMessage);
   }
   
   public IUserDefinedKeyword performFinish() {
      Set<String> keywords = computeKeywords();
      if (keywords.isEmpty()) {
         return null;
      }

      final IKeywordSort sort = (IKeywordSort) this.sortCombo
            .getData(this.sortCombo.getItem(this.sortCombo.getSelectionIndex()));

      final IUserDefinedKeywordContentDescription contentDescription = (IUserDefinedKeywordContentDescription) this.contentCombo
            .getData(this.contentCombo.getItem(this.contentCombo
                  .getSelectionIndex()));

      final String description = this.descriptionText.getText();

      final Character closingCharacter;
      if (this.closingCharacterCombo.getSelectionIndex() == 0) {
         closingCharacter = null;
      }
      else {
         closingCharacter = this.closingCharacterCombo.getItem(
               this.closingCharacterCombo.getSelectionIndex()).charAt(0);
      }

      final IUserDefinedKeyword keyword2Save = new UserDefinedKeyword(keywords, sort, contentDescription, description, closingCharacter);
      return keyword2Save;
   }
   
   protected Set<String> computeKeywords() {
      final String formattedKeyword = this.keywordText.getText();
      final Set<String> keywords = new HashSet<String>();
      for (final String kw : formattedKeyword.split(",")) {
         if (!StringUtil.isTrimmedEmpty(kw)) {
            keywords.add(kw.trim());
         }
      }
      return keywords;
   }
}
