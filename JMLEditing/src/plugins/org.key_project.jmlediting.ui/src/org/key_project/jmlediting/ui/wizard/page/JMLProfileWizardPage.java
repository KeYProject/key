package org.key_project.jmlediting.ui.wizard.page;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.Date;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Random;
import java.util.Set;

import org.eclipse.core.resources.IProject;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.fieldassist.ControlDecoration;
import org.eclipse.jface.fieldassist.FieldDecorationRegistry;
import org.eclipse.jface.layout.TableColumnLayout;
import org.eclipse.jface.viewers.ArrayContentProvider;
import org.eclipse.jface.viewers.CheckboxTableViewer;
import org.eclipse.jface.viewers.ColumnWeightData;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.viewers.TableViewerColumn;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.key_project.jmlediting.core.profile.IEditableDerivedProfile;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.InvalidProfileException;
import org.key_project.jmlediting.core.profile.JMLProfileHelper;
import org.key_project.jmlediting.core.profile.JMLProfileManagement;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.core.profile.syntax.user.IUserDefinedKeyword;
import org.key_project.jmlediting.ui.preferencepages.RebuildHelper;
import org.key_project.jmlediting.ui.preferencepages.RebuildHelper.UserMessage;
import org.key_project.jmlediting.ui.provider.KeywordLabelProvider;
import org.key_project.jmlediting.ui.provider.UserDefinedKeywordLabelProvider;
import org.key_project.jmlediting.ui.util.JMLEditingImages;
import org.key_project.jmlediting.ui.util.JMLSWTUtil;
import org.key_project.jmlediting.ui.wizard.JMLKeywordWizard;
import org.key_project.jmlediting.ui.wizard.JMLProfileWizard;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.CollectionUtil;

/**
 * The {@link WizardPage} to edit {@link IJMLProfile}s.
 * @author Martin Hentschel
 * @see JMLProfileWizard
 */
public class JMLProfileWizardPage extends WizardPage {
   /**
    * error text if profile name already exists.
    */
   public static final String NAME_EXISTS = "Profile Name already exists!";
   
   /**
    * error text if no profile to derive from is selected.
    */
   public static final String PLEASE_SELECT = "Please select a profile to derive from!";
   
   /**
    * error text if profile name is empty.
    */
   public static final String PLEASE_FILL = "Profile Name must not be empty!";

   /**
    * the JMLProfile to view (null indicates new Profile).
    */
   private final IJMLProfile parentProfile;
   
   /**
    * the JMLProfile to edit.
    */
   private IEditableDerivedProfile profileToEdit;

   /**
    * the table to show predefined keywords.
    */
   private TableViewer keywordTableViewer;
   
   /**
    * the table to show all user defined keywords.
    */
   private TableViewer derivedTableViewer;

   /**
    * The button to create new user defined keywords.
    */
   private Button derivedKeywordNewButton;
   
   /**
    * the button to edit user defined keywords.
    */
   private Button derivedKeywordEditButton;
   
   /**
    * the button to remove user defined keywords.
    */
   private Button derivedKeywordRemoveButton;

   /**
    * the Widget containing the profile name.
    */
   private Text profileNameText;
   
   /**
    * the Widget to display keyword validation errors.
    */
   private ControlDecoration profileNameError;
   
   /**
    * the Widget containing the available Profiles to derive from.
    */
   private Combo derivedFromCombo;
   
   /**
    * the Widget to display deriveFrom validation errors.
    */
   private ControlDecoration comboError;
   
   /**
    * the comparator of Keywords to display them in lexical order.
    */
   private final Comparator<IKeyword> keywordComparator = new Comparator<IKeyword>() {
      @Override
      public int compare(final IKeyword o1, final IKeyword o2) {
         return o1.getKeywords().iterator().next().compareTo(o2.getKeywords().iterator().next());
      }
   };

   public JMLProfileWizardPage(String pageName, final IJMLProfile profile) {
      super(pageName);
      this.parentProfile = profile;
      setImageDescriptor(JMLEditingImages.getImageDescriptor(JMLEditingImages.JML_WIZARD));
      if (profile != null && profile instanceof IEditableDerivedProfile) {
         this.profileToEdit = (IEditableDerivedProfile) profile;
      }
      if (this.parentProfile == null) {
         setTitle("Create Profile");
         setMessage("Define the content of the new profile.");
      }
      else {
         if (this.profileToEdit == null) {
            setTitle("View Profile");
            setMessage("Inspect the content of the profile.");
         }
         else {
            setTitle("Edit Profile");
            setMessage("Edit the content of the existing profile.");
         }
      }
   }

   @Override
   public void createControl(Composite parent) {
      final Composite myComposite = new Composite(parent, SWT.NONE);
      setControl(myComposite);
      myComposite.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
      myComposite.setLayout(new GridLayout(3, false));

      if (this.parentProfile == null || (this.parentProfile != null && this.profileToEdit != null)) {
         this.addProfileName(myComposite, true);
         this.addDerivedFrom(myComposite, this.parentProfile == null);
         if (this.parentProfile != null) {
            this.profileNameText.setText(this.parentProfile.getName());
         }

         this.addKeywordTableLabel(myComposite, "Keywords from parent profile:");
         this.addKeywordTable(myComposite, true);

         this.addDerivedTableLabel(myComposite);
         this.addDerivedTable(myComposite);
         this.addDerivedButtons(myComposite);
      }
      else {
         this.addProfileName(myComposite, false);
         this.profileNameText.setText(this.parentProfile.getName());
         this.addKeywordTableLabel(myComposite, "Supported Keywords");

         this.addKeywordTable(myComposite, false);
      }

      this.fillKeywordTable();
      if (this.profileToEdit != null) {
         this.derivedFromCombo.select(this.getComboIndexForProfile(this.profileToEdit.getParentProfile()));
      }
      this.fillDerivedTable();
      
      updatePageCompleted();
   }

   protected void addProfileName(final Composite myComposite, final boolean editable) {
      final Label profileNameLabel = new Label(myComposite, SWT.NONE);
      profileNameLabel.setText("Profile Name:");

      GridData gridData = new GridData(GridData.FILL_HORIZONTAL);
      gridData.horizontalSpan = 2;
      this.profileNameText = new Text(myComposite, SWT.SINGLE | SWT.BORDER);
      this.profileNameText.setLayoutData(gridData);
      this.profileNameText.setEditable(editable);

      this.profileNameError = new ControlDecoration(this.profileNameText, SWT.RIGHT | SWT.TOP);
      this.profileNameError.setImage(FieldDecorationRegistry.getDefault().getFieldDecoration(FieldDecorationRegistry.DEC_ERROR).getImage());
      this.profileNameError.setDescriptionText(PLEASE_FILL);
      this.profileNameError.hide();

      this.profileNameText.addModifyListener(new ModifyListener() {
         @Override
         public void modifyText(final ModifyEvent e) {
            updatePageCompleted();
         }
      });
   }

   protected void addDerivedFrom(final Composite myComposite, final boolean enabled) {
      final Label derivedFromLabel = new Label(myComposite, SWT.NONE);
      derivedFromLabel.setText("Derived from:");

      GridData gridData = new GridData(GridData.FILL_HORIZONTAL);
      gridData.horizontalSpan = 2;
      this.derivedFromCombo = new Combo(myComposite, SWT.BORDER | SWT.READ_ONLY);
      this.derivedFromCombo.setLayoutData(gridData);
      JMLSWTUtil.fillComboWithParentProfilesAndDate(this.derivedFromCombo);
      this.derivedFromCombo.setEnabled(enabled);

      this.comboError = new ControlDecoration(this.derivedFromCombo, SWT.RIGHT | SWT.TOP);
      this.comboError.setImage(FieldDecorationRegistry.getDefault().getFieldDecoration(FieldDecorationRegistry.DEC_ERROR).getImage());
      this.comboError.setDescriptionText(PLEASE_SELECT);
      this.comboError.hide();
      
      this.derivedFromCombo.addModifyListener(new ModifyListener() {
         @Override
         public void modifyText(final ModifyEvent e) {
            fillKeywordTable();
            fillDerivedTable();
            updatePageCompleted();
         }
      });
   }

   private Button createTableSideButton(final Composite myComposite, final String name) {
      final Button button = new Button(myComposite, SWT.PUSH);
      button.setText(name);
      button.setLayoutData(new GridData(SWT.FILL, SWT.TOP, false, false, 1, 1));
      return button;
   }

   private void addKeywordTableLabel(final Composite myComposite, final String text) {
      GridData gridData = new GridData(GridData.FILL_HORIZONTAL);
      gridData.horizontalSpan = 3;
      gridData.verticalIndent = 20;
      final Label keywordTableLabel = new Label(myComposite, SWT.NONE);
      keywordTableLabel.setText(text);
      keywordTableLabel.setLayoutData(gridData);
   }

   private void addDerivedTableLabel(final Composite myComposite) {
      GridData gridData = new GridData(GridData.FILL_HORIZONTAL);
      gridData.horizontalSpan = 3;
      gridData.verticalIndent = 20;
      final Label derivedTableLabel = new Label(myComposite, SWT.NONE);
      derivedTableLabel.setText("Custom Keywords:");
      derivedTableLabel.setLayoutData(gridData);
   }

   private void addKeywordTable(final Composite myComposite, final boolean derived) {
      GridData gridData = new GridData(GridData.FILL_HORIZONTAL);
      gridData.horizontalSpan = 2;
      gridData.heightHint = 200;
      Composite tableComposite = new Composite(myComposite, SWT.NONE);
      tableComposite.setLayoutData(gridData);
      TableColumnLayout tableLayout = new TableColumnLayout();
      tableComposite.setLayout(tableLayout);

      int style = SWT.H_SCROLL | SWT.V_SCROLL | SWT.BORDER | SWT.FULL_SELECTION;
      if (derived) {
         style = style | SWT.CHECK | SWT.MULTI;
         this.keywordTableViewer = CheckboxTableViewer.newCheckList(tableComposite, style);
      }
      else {
         this.keywordTableViewer = new TableViewer(tableComposite, style);
      }
      this.keywordTableViewer.getTable().setHeaderVisible(true);
      this.keywordTableViewer.getTable().setLinesVisible(true);

      final TableViewerColumn genericKeywordTableColumn = new TableViewerColumn(this.keywordTableViewer, SWT.LEFT);
      genericKeywordTableColumn.getColumn().setText("Keyword");
      tableLayout.setColumnData(genericKeywordTableColumn.getColumn(), new ColumnWeightData(40));

      final TableViewerColumn genericDescriptionTableColumn = new TableViewerColumn(this.keywordTableViewer, SWT.LEFT);
      genericDescriptionTableColumn.getColumn().setText("Description");
      tableLayout.setColumnData(genericDescriptionTableColumn.getColumn(), new ColumnWeightData(60));
      
      this.keywordTableViewer.setContentProvider(ArrayContentProvider.getInstance());
      this.keywordTableViewer.setLabelProvider(new KeywordLabelProvider());
   }

   private void fillKeywordTable() {
      if (this.keywordTableViewer != null) {
         final List<IKeyword> keywordList;
         if (this.profileToEdit != null) {
            keywordList = new ArrayList<IKeyword>(this.profileToEdit.getParentProfile().getSupportedKeywords());
         }
         else if (this.parentProfile != null) {
            keywordList = new ArrayList<IKeyword>(this.parentProfile.getSupportedKeywords());
         }
         else if (this.derivedFromCombo != null && this.getSelectedProfileFromCombo() != null) {
             keywordList = new ArrayList<IKeyword>(this.getSelectedProfileFromCombo().getSupportedKeywords());
         }
         else {
            keywordList = new ArrayList<IKeyword>();
         }
         Collections.sort(keywordList, this.keywordComparator);
         keywordTableViewer.setInput(keywordList);
         
         if (keywordTableViewer instanceof CheckboxTableViewer) {
            CheckboxTableViewer ctv = (CheckboxTableViewer)keywordTableViewer;
            for (final IKeyword keyword : keywordList) {
               boolean checked = this.profileToEdit != null ? 
                                 !this.profileToEdit.isParentKeywordDisabled(keyword) : 
                                 true;
               ctv.setChecked(keyword, checked);
            }
         }
      }
   }

   private String generateId(final String profileName) {
      String result = "user.defined.profile."
            + profileName.replaceAll("\\s", "");
      final Random rnd = new Random(new Date().getTime());
      while (JMLProfileManagement.instance().getProfileFromIdentifier(result) != null) {
         result += rnd.nextInt(9);
      }

      return result;
   }

   private void addDerivedButtons(final Composite myComposite) {
      this.derivedKeywordNewButton = this.createTableSideButton(myComposite, "New...");
      this.derivedKeywordNewButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(final SelectionEvent e) {
            createDerivedKeyword();
         }
      });
      this.derivedKeywordEditButton = this.createTableSideButton(myComposite,"Edit...");
      this.derivedKeywordEditButton.addSelectionListener(new SelectionAdapter() {
               @Override
               public void widgetSelected(final SelectionEvent e) {
                  editDerivedKeyword();
               }
            });

      this.derivedKeywordRemoveButton = this.createTableSideButton(myComposite, "Remove...");
      this.derivedKeywordRemoveButton.addSelectionListener(new SelectionAdapter() {
               @Override
               public void widgetSelected(final SelectionEvent e) {
                  removeDerivedKeyword();
               }
            });
   }
   
   protected void createDerivedKeyword() {
      IEditableDerivedProfile tempProfile = profileToEdit != null ? 
                                            profileToEdit : 
                                            deriveProfile();
      if (supportsNewKeywords(tempProfile)) {
         IUserDefinedKeyword newKeyword = JMLKeywordWizard.openWizard(getShell(), tempProfile, null);
         if (newKeyword != null) {
            @SuppressWarnings("unchecked")
            List<IKeyword> keywords = (List<IKeyword>)derivedTableViewer.getInput();
            keywords.add(newKeyword);
            derivedTableViewer.setInput(keywords);
            derivedTableViewer.setSelection(SWTUtil.createSelection(newKeyword));
            updateDerivedEditAndRemoveEnabled();
         }
      }
   }

   protected boolean supportsNewKeywords(IEditableDerivedProfile tempProfile) {
      return tempProfile != null && !tempProfile.getAvailableKeywordSorts().isEmpty();
   }

   protected void editDerivedKeyword() {
      final IUserDefinedKeyword oldKeyword = JMLProfileWizardPage.this.getSelectedDerivedKeyword();
      if (oldKeyword == null) {
         return;
      }
      IEditableDerivedProfile tempProfile = profileToEdit != null ? 
                                            profileToEdit : 
                                            deriveProfile();
      if (supportsNewKeywords(tempProfile)) {
         IUserDefinedKeyword newKeyword = JMLKeywordWizard.openWizard(getShell(), tempProfile, oldKeyword);
         if (newKeyword != null) {
            @SuppressWarnings("unchecked")
            List<IKeyword> keywords = (List<IKeyword>)derivedTableViewer.getInput();
            int index = keywords.indexOf(oldKeyword);
            keywords.remove(index);
            keywords.add(index, newKeyword);
            derivedTableViewer.setInput(keywords);
            derivedTableViewer.setSelection(SWTUtil.createSelection(newKeyword));
            updateDerivedEditAndRemoveEnabled();
         }
      }
   }

   protected void removeDerivedKeyword() {
      final IUserDefinedKeyword keyword = JMLProfileWizardPage.this.getSelectedDerivedKeyword();
      if (keyword == null) {
         return;
      }
      final boolean remove = MessageDialog.openConfirm(JMLProfileWizardPage.this.getShell(), "Remove Keyword", "Are you reall sure to remove the keyword \"" + CollectionUtil.toString(keyword.getKeywords()) + "\"?");
      if (remove) {
         @SuppressWarnings("unchecked")
         List<IKeyword> keywords = (List<IKeyword>)derivedTableViewer.getInput();
         keywords.remove(keyword);
         derivedTableViewer.setInput(keywords);
         updateDerivedEditAndRemoveEnabled();
      }
   }

   private void addDerivedTable(final Composite myComposite) {
      GridData gridData = new GridData(GridData.FILL_HORIZONTAL);
      gridData.horizontalSpan = 2;
      gridData.verticalSpan = 3;
      gridData.heightHint = 200;
      Composite tableComposite = new Composite(myComposite, SWT.NONE);
      tableComposite.setLayoutData(gridData);
      TableColumnLayout tableLayout = new TableColumnLayout();
      tableComposite.setLayout(tableLayout);

      this.derivedTableViewer = new TableViewer(tableComposite, SWT.H_SCROLL | SWT.V_SCROLL | SWT.BORDER | SWT.FULL_SELECTION);
      this.derivedTableViewer.getTable().setHeaderVisible(true);
      this.derivedTableViewer.getTable().setLinesVisible(true);

      this.derivedTableViewer.getTable().addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(final SelectionEvent e) {
            updateDerivedEditAndRemoveEnabled();
         }
      });

      final TableViewerColumn genericKeywordTableColumn = new TableViewerColumn(this.derivedTableViewer, SWT.LEFT);
      genericKeywordTableColumn.getColumn().setText("Keyword");
      tableLayout.setColumnData(genericKeywordTableColumn.getColumn(), new ColumnWeightData(30));

      final TableViewerColumn genericContentTableColumn = new TableViewerColumn(this.derivedTableViewer, SWT.LEFT);
      genericContentTableColumn.getColumn().setText("Content");
      tableLayout.setColumnData(genericContentTableColumn.getColumn(), new ColumnWeightData(35));

      final TableViewerColumn genericDescriptionTableColumn = new TableViewerColumn(this.derivedTableViewer, SWT.LEFT);
      genericDescriptionTableColumn.getColumn().setText("Description");
      tableLayout.setColumnData(genericDescriptionTableColumn.getColumn(), new ColumnWeightData(35));
      
      this.derivedTableViewer.setContentProvider(ArrayContentProvider.getInstance());
      this.derivedTableViewer.setLabelProvider(new UserDefinedKeywordLabelProvider());
   }

   private void fillDerivedTable() {
      if (this.derivedTableViewer == null) {
         return;
      }
      final List<IKeyword> keywordList = this.profileToEdit != null ?
                                         new LinkedList<IKeyword>(this.profileToEdit.getAdditionalKeywords()) :
                                         new LinkedList<IKeyword>();
      Collections.sort(keywordList, this.keywordComparator);
      derivedTableViewer.setInput(keywordList);
      updateDerivedEditAndRemoveEnabled();
   }

   protected void updateDerivedEditAndRemoveEnabled() {
      boolean enabled = getSelectedDerivedKeyword() != null;
      JMLProfileWizardPage.this.derivedKeywordEditButton.setEnabled(enabled);
      JMLProfileWizardPage.this.derivedKeywordRemoveButton.setEnabled(enabled);
   }

   private IUserDefinedKeyword getSelectedDerivedKeyword() {
      return (IUserDefinedKeyword)SWTUtil.getFirstElement(this.derivedTableViewer.getSelection());
   }

   private int getComboIndexForProfile(final IJMLProfile profile) {
      for (int i = 0; i < this.derivedFromCombo.getItemCount(); i++) {
         if (this.derivedFromCombo.getItems()[i].equals(profile.getName())) {
            return i;
         }
      }
      return 0;
   }

   private IJMLProfile getSelectedProfileFromCombo() {
      if (derivedFromCombo != null) {
         final int index = this.derivedFromCombo.getSelectionIndex();
         if (index == -1) {
            return null;
         }
         else {
            return (IJMLProfile) this.derivedFromCombo.getData(this.derivedFromCombo.getItem(index));
         }
      }
      else {
         return null;
      }
   }
   
   protected IEditableDerivedProfile deriveProfile() {
      final String profileName = this.profileNameText.getText();
      final String profileId = this.generateId(profileName);
      final IJMLProfile parentProfile = this.getSelectedProfileFromCombo();

      if (profileName.isEmpty()) {
         return null;
      }
      if (parentProfile == null) {
         return null;
      }
      if (!this.isProfileNameUnique(profileName)) {
         return null;
      }

      IEditableDerivedProfile result = parentProfile.derive(profileId, profileName);
      updateProfileWithUIContent(result);
      return result;
   }
   
   protected void updateProfileWithUIContent(IEditableDerivedProfile profile) {
      profile.setName(profileNameText.getText());
      if (keywordTableViewer instanceof CheckboxTableViewer) {
         CheckboxTableViewer ctv = (CheckboxTableViewer) keywordTableViewer;
         @SuppressWarnings("unchecked")
         List<IKeyword> keywords = (List<IKeyword>)keywordTableViewer.getInput();
         for (IKeyword keyword : keywords) {
            profile.setParentKeywordDisabled(keyword, !ctv.getChecked(keyword));
         }
      }
      
      if (derivedTableViewer != null) {
         // Get old keywords
         Set<IKeyword> remainingKeywords = new HashSet<IKeyword>(profile.getAdditionalKeywords());
         // Add new keywords
         @SuppressWarnings("unchecked")
         List<IKeyword> keywords = (List<IKeyword>)derivedTableViewer.getInput();
         for (IKeyword keyword : keywords) {
            if (!remainingKeywords.remove(keyword)) {
               profile.addKeyword(keyword);
            }
         }
         // Remove remaining old keywords
         for (IKeyword keyword : remainingKeywords) {
            profile.removeKeyword(keyword);
         }
      }
   }
   
   protected void updatePageCompleted() {
      // Validate name (if editable)
      String errorMessage = null;
      if ((profileNameText.getStyle() & SWT.READ_ONLY) != SWT.READ_ONLY) {
         if (profileNameText.getText().isEmpty()) {
            profileNameError.setDescriptionText(PLEASE_FILL);
            profileNameError.show();
            errorMessage = profileNameError.getDescriptionText();
         }
         else {
            IJMLProfile existingProfile = JMLProfileManagement.instance().getProfileFromName(profileNameText.getText());
            if (existingProfile != null && existingProfile != profileToEdit) {
               profileNameError.setDescriptionText(NAME_EXISTS);
               profileNameError.show();
               errorMessage = profileNameError.getDescriptionText();
            }
            else {
               profileNameError.hide();
            }
         }
      }
      // Validate derived from (if available)
      if (JMLProfileWizardPage.this.derivedFromCombo != null) {
         if (JMLProfileWizardPage.this.derivedFromCombo.getSelectionIndex() == -1) {
            JMLProfileWizardPage.this.comboError.show();
            if (errorMessage == null) {
               errorMessage = comboError.getDescriptionText();
            }
         }
         else {
            JMLProfileWizardPage.this.comboError.hide();
         }
      }
      // Update buttons
      if (derivedKeywordNewButton != null) {
         derivedKeywordNewButton.setEnabled(profileToEdit != null ? 
                                            supportsNewKeywords(profileToEdit) : 
                                            supportsNewKeywords(deriveProfile()));
      }
      // Update page completion
      setPageComplete(errorMessage == null);
      setErrorMessage(errorMessage);
   }

   private boolean isProfileNameUnique(final String profileName) {
      if (JMLProfileManagement.instance().getProfileFromName(profileName) != null) {
         return false;
      }
      else {
         return true;
      }
   }

   public IEditableDerivedProfile performFinish() {
      IEditableDerivedProfile profileToSave;
      if (this.parentProfile == null) {
         profileToSave = deriveProfile();
      }
      else if (this.profileToEdit != null) {
         profileToSave = profileToEdit;
         updateProfileWithUIContent(profileToSave);
      }
      else {
         profileToSave = null;
      }
      if (profileToSave != null) {
         this.triggerRebuild(profileToSave);
      }
      return profileToSave;
   }

   private void triggerRebuild(final IEditableDerivedProfile profileToSave) {
      if (profileToSave == null) {
         return;
      }
      final Set<IProject> affectedProjects = JMLProfileHelper.getProjectsUsingProfile(profileToSave);
      final Runnable preferencesUpdater = new Runnable() {
         @Override
         public void run() {
            try {
               if (JMLProfileWizardPage.this.parentProfile == null) {
                  JMLProfileManagement.instance().addUserDefinedProfile(profileToSave);
               }
               JMLProfileManagement.instance().writeDerivedProfiles();
            }
            catch (final InvalidProfileException ipe) {
               ipe.printStackTrace();
               return;
            }
         }
      };
      RebuildHelper.triggerRebuild(affectedProjects, this.getShell(), UserMessage.PROFILE_EDITED, preferencesUpdater);
   }
}
