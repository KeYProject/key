package org.key_project.jmlediting.ui.preferencepages.profileDialog;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.Date;
import java.util.Iterator;
import java.util.List;
import java.util.Random;
import java.util.Set;

import org.eclipse.core.resources.IProject;
import org.eclipse.jface.dialogs.IMessageProvider;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.dialogs.TitleAreaDialog;
import org.eclipse.jface.fieldassist.ControlDecoration;
import org.eclipse.jface.fieldassist.FieldDecorationRegistry;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;
import org.eclipse.swt.widgets.TableItem;
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
import org.key_project.jmlediting.ui.util.JMLSWTUtil;

/**
 * A dialog to view, create and edit JMLProfiles.
 *
 * @author Thomas Glaser
 *
 */
public class JMLProfileDialog extends TitleAreaDialog {
   /**
    * error text if profile name already exists.
    */
   private static final String NAME_EXISTS = "Profile Name already exists!";
   /**
    * error text if no profile to derive from is selected.
    */
   private static final String PLEASE_SELECT = "Please select a profile to derive from!";
   /**
    * error text if profile name is empty.
    */
   private static final String PLEASE_FILL = "Profile Name must not be empty!";

   /**
    * the JMLProfile to view (null indicates new Profile).
    */
   private final IJMLProfile profile;
   /**
    * the JMLProfile to edit.
    */
   private IEditableDerivedProfile derivedProfile;

   /**
    * the table to show predefined keywords.
    */
   private Table keywordTable;
   /**
    * the table to show all user defined keywords.
    */
   private Table derivedTable;
   /**
    * the button to edit user defined keywords.
    */
   private Button derivedKeywordEditButton;
   /**
    * the button to remove user defined keywords.
    */
   private Button derivedKeywordRemoveButton;

   /**
    * the title of the dialog.
    */
   private final String title;
   /**
    * the message of the dialog.
    */
   private final String message;

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
         return o1.getKeywords().iterator().next()
               .compareTo(o2.getKeywords().iterator().next());
      }
   };

   /**
    * the only Constructor.
    *
    * @param parent
    *           the parent shell
    * @param profile
    *           the profile to view/edit (instanceof IEditableDerivedProfile
    *           when edit, and null when new Profile)
    */
   public JMLProfileDialog(final Shell parent, final IJMLProfile profile) {
      super(parent);
      this.profile = profile;
      if (profile != null && profile instanceof IEditableDerivedProfile) {
         this.derivedProfile = (IEditableDerivedProfile) profile;
      }
      if (this.profile == null) {
         this.title = "JML Profile Creator";
         this.message = "";
      }
      else {
         this.message = "Profile ID: " + profile.getIdentifier();
         if (this.derivedProfile == null) {
            this.title = "JML Profile Viewer";
         }
         else {
            this.title = "JML Profile Editor";
         }
      }
      this.setHelpAvailable(false);
   }

   @Override
   public void create() {
      super.create();
      this.setTitle(this.title);
      if (!this.message.isEmpty()) {
         this.setMessage(this.message, IMessageProvider.INFORMATION);
      }
      else {
         this.setMessage(this.message);
      }
   }

   @Override
   protected Control createDialogArea(final Composite parent) {
      final Composite composite = (Composite) super.createDialogArea(parent);
      final Composite myComposite = new Composite(composite, SWT.NONE);
      myComposite.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
      myComposite.setLayout(new GridLayout(3, false));

      if (this.profile == null
            || (this.profile != null && this.derivedProfile != null)) {
         this.addProfileName(myComposite, true);
         this.addDerivedFrom(myComposite, this.profile == null);
         if (this.profile == null) {
            this.derivedFromCombo.addSelectionListener(new SelectionListener() {

               @Override
               public void widgetSelected(final SelectionEvent e) {
                  System.out.println("selected derivedFromCombo");
                  JMLProfileDialog.this.fillKeywordTable();
               }

               @Override
               public void widgetDefaultSelected(final SelectionEvent e) {
               }
            });
         }
         else {
            this.profileNameText.setText(this.profile.getName());
         }

         this.addKeywordTableLabel(myComposite, "Keywords from parent profile:");
         this.addKeywordTable(myComposite, true);
         this.keywordTable.addSelectionListener(new SelectionListener() {
            @Override
            public void widgetSelected(final SelectionEvent e) {
               if (e.detail == SWT.CHECK) {
                  final IKeyword selectedKeyword = JMLProfileDialog.this
                        .getParentKeyword4TableItem((TableItem) e.item);
                  if (JMLProfileDialog.this.derivedProfile == null
                        && !JMLProfileDialog.this.saveNewProfile(false)) {
                     return;
                  }
                  JMLProfileDialog.this.derivedProfile
                        .setParentKeywordDisabled(selectedKeyword,
                              !JMLProfileDialog.this.derivedProfile
                                    .isParentKeywordDisabled(selectedKeyword));
               }
            };

            @Override
            public void widgetDefaultSelected(final SelectionEvent e) {
            }
         });
         this.addDerivedTableLabel(myComposite);

         this.addDerivedTable(myComposite);

         this.addDerivedButtons(myComposite);
      }
      else {
         this.addProfileName(myComposite, false);
         this.profileNameText.setText(this.profile.getName());
         this.addKeywordTableLabel(myComposite, "Supported Keywords");

         this.addKeywordTable(myComposite, false);
      }

      this.fillKeywordTable();
      if (this.derivedProfile != null) {
         this.derivedFromCombo
               .select(this.getComboIndexForProfile(this.derivedProfile
                     .getParentProfile()));
         this.fillDerivedTable();
      }

      return composite;
   }

   private Button createTableSideButton(final Composite myComposite,
         final String name) {
      final Button button = new Button(myComposite, SWT.PUSH);
      button.setText(name);
      button.setLayoutData(new GridData(SWT.FILL, SWT.TOP, false, false, 1, 1));

      return button;
   }

   private String[] keywordToTableData(final IKeyword keyword) {
      String sourceDescription = keyword.getDescription();
      if (sourceDescription != null && sourceDescription.length() > 200) {
         sourceDescription = sourceDescription.substring(0, 196);
         sourceDescription += " ...";
         sourceDescription = sourceDescription.replace('\n', ' ');
      }
      final Iterator<String> iterator = keyword.getKeywords().iterator();
      String keywordString = iterator.next();
      while (iterator.hasNext()) {
         keywordString = keywordString + ", " + iterator.next();
      }

      return new String[] { keywordString, sourceDescription };
   }

   private void addDerivedFrom(final Composite myComposite,
         final boolean enabled) {
      GridData data;
      data = new GridData(SWT.FILL, SWT.TOP, false, true);
      final Label derivedFromLabel = new Label(myComposite, SWT.NONE);
      derivedFromLabel.setText("Derived from:");
      derivedFromLabel.setLayoutData(data);

      data = new GridData(SWT.LEFT, SWT.TOP, true, true);
      data.horizontalSpan = 2;
      data.widthHint = 200;
      this.derivedFromCombo = new Combo(myComposite, SWT.BORDER | SWT.READ_ONLY);
      this.derivedFromCombo.setLayoutData(data);
      JMLSWTUtil.fillComboWithParentProfilesAndDate(this.derivedFromCombo);
      this.derivedFromCombo.setEnabled(enabled);

      this.comboError = new ControlDecoration(this.derivedFromCombo, SWT.RIGHT
            | SWT.TOP);
      this.comboError.setImage(FieldDecorationRegistry.getDefault()
            .getFieldDecoration(FieldDecorationRegistry.DEC_ERROR).getImage());
      this.comboError.setDescriptionText(PLEASE_SELECT);
      this.comboError.show();

      this.derivedFromCombo.addModifyListener(new ModifyListener() {
         @Override
         public void modifyText(final ModifyEvent e) {
            final int index = JMLProfileDialog.this.derivedFromCombo
                  .getSelectionIndex();
            if (index == -1) {
               JMLProfileDialog.this.comboError.show();
            }
            else {
               JMLProfileDialog.this.comboError.hide();
            }
         }
      });
   }

   private void addProfileName(final Composite myComposite,
         final boolean enabled) {
      GridData data;
      data = new GridData(SWT.FILL, SWT.TOP, false, true);
      data.horizontalSpan = 1;
      final Label profileNameLabel = new Label(myComposite, SWT.NONE);
      profileNameLabel.setText("Profile Name:");
      profileNameLabel.setLayoutData(data);

      data = new GridData(SWT.LEFT, SWT.TOP, true, true, 2, 1);
      data.widthHint = 200;
      this.profileNameText = new Text(myComposite, SWT.SINGLE | SWT.BORDER);
      this.profileNameText.setLayoutData(data);
      this.profileNameText.setEnabled(enabled);

      this.profileNameError = new ControlDecoration(this.profileNameText,
            SWT.RIGHT | SWT.TOP);
      this.profileNameError.setImage(FieldDecorationRegistry.getDefault()
            .getFieldDecoration(FieldDecorationRegistry.DEC_ERROR).getImage());
      this.profileNameError.setDescriptionText(PLEASE_FILL);
      this.profileNameError.show();

      this.profileNameText.addModifyListener(new ModifyListener() {
         @Override
         public void modifyText(final ModifyEvent e) {
            if (JMLProfileDialog.this.profileNameText.getText().isEmpty()) {
               JMLProfileDialog.this.profileNameError
                     .setDescriptionText(JMLProfileDialog.PLEASE_FILL);
               JMLProfileDialog.this.profileNameError.show();
            }
            else {
               JMLProfileDialog.this.profileNameError.hide();
            }
         }
      });
   }

   private void addKeywordTableLabel(final Composite myComposite,
         final String text) {
      GridData data;
      data = new GridData(SWT.LEFT, SWT.TOP, false, false, 3, 1);
      data.verticalIndent = 20;
      final Label keywordTableLabel = new Label(myComposite, SWT.NONE);
      keywordTableLabel.setText(text);
      keywordTableLabel.setLayoutData(data);
   }

   private void addDerivedTableLabel(final Composite myComposite) {
      GridData data;
      data = new GridData(SWT.LEFT, SWT.TOP, false, false, 3, 1);
      data.verticalIndent = 20;
      final Label derivedTableLabel = new Label(myComposite, SWT.NONE);
      derivedTableLabel.setText("Custom Keywords:");
      derivedTableLabel.setLayoutData(data);
   }

   private void addKeywordTable(final Composite myComposite,
         final boolean derived) {
      GridData data;
      data = new GridData(SWT.FILL, SWT.TOP, true, true, 2, 1);
      int style = SWT.H_SCROLL | SWT.V_SCROLL | SWT.BORDER | SWT.FULL_SELECTION;
      if (derived) {
         style = style | SWT.CHECK | SWT.MULTI;
         data.heightHint = 200;
      }
      else {
         data.heightHint = 400;
      }
      this.keywordTable = new Table(myComposite, style);
      this.keywordTable.setLayoutData(data);
      this.keywordTable.setHeaderVisible(true);
      this.keywordTable.setLinesVisible(true);

      final TableColumn genericKeywordTableColumn = new TableColumn(
            this.keywordTable, SWT.LEFT);
      genericKeywordTableColumn.setText("Keyword");
      genericKeywordTableColumn.setWidth(150);

      final TableColumn genericDescriptionTableColumn = new TableColumn(
            this.keywordTable, SWT.LEFT);
      genericDescriptionTableColumn.setText("Description");
      genericDescriptionTableColumn.setWidth(300);
   }

   private IKeyword getParentKeyword4TableItem(final TableItem selectedItem) {
      if (selectedItem == null) {
         return null;
      }
      return (IKeyword) selectedItem.getData();
   }

   private void fillKeywordTable() {
      if (this.keywordTable == null) {
         return;
      }

      this.keywordTable.removeAll();

      final List<IKeyword> keywordList;
      if (this.profile != null && this.derivedProfile != null) {
         keywordList = new ArrayList<IKeyword>(this.derivedProfile
               .getParentProfile().getSupportedKeywords());
      }
      else if (this.profile != null) {
         keywordList = new ArrayList<IKeyword>(
               this.profile.getSupportedKeywords());
      }
      else if (this.saveNewProfile(false)) {
         keywordList = new ArrayList<IKeyword>(this.derivedProfile
               .getParentProfile().getSupportedKeywords());
      }
      else if (this.derivedFromCombo != null
            && this.getSelectedProfileFromCombo() != null) {
         keywordList = new ArrayList<IKeyword>(this
               .getSelectedProfileFromCombo().getSupportedKeywords());
      }
      else {
         return;
      }

      Collections.sort(keywordList, this.keywordComparator);
      for (final IKeyword keyword : keywordList) {
         final TableItem item = new TableItem(this.keywordTable, SWT.NONE);
         item.setText(this.keywordToTableData(keyword));
         item.setData(keyword);
         if (this.derivedProfile != null) {
            item.setChecked(!this.derivedProfile
                  .isParentKeywordDisabled(keyword));
         }
         else {
            item.setChecked(true);
         }
      }
      this.keywordTable.setEnabled(true);
      this.keywordTable.redraw();
   }

   private boolean isProfileNameUnique(final String profileName) {
      if (JMLProfileManagement.instance().getProfileFromName(profileName) != null) {
         this.profileNameError.setDescriptionText(NAME_EXISTS);
         this.profileNameError.show();
         return false;
      }
      else {
         this.setMessage("", IMessageProvider.NONE);
         this.profileNameError.hide();
         return true;
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
      final Button derivedKeywordNewButton = this.createTableSideButton(
            myComposite, "New...");
      derivedKeywordNewButton.addSelectionListener(new SelectionListener() {
         @Override
         public void widgetSelected(final SelectionEvent e) {
            if (JMLProfileDialog.this.derivedProfile == null) {
               final IJMLProfile parentProfile = JMLProfileDialog.this
                     .getSelectedProfileFromCombo();
               if (parentProfile == null) {
                  return;
               }
               if (!JMLProfileDialog.this.saveNewProfile(false)) {
                  return;
               }
            }
            final JMLKeywordDialog dialog = new JMLKeywordDialog(
                  JMLProfileDialog.this.getShell(),
                  JMLProfileDialog.this.derivedProfile, null);
            dialog.open();
            JMLProfileDialog.this.fillDerivedTable();
         }

         @Override
         public void widgetDefaultSelected(final SelectionEvent e) {
         }
      });
      this.derivedKeywordEditButton = this.createTableSideButton(myComposite,
            "Edit...");
      this.derivedKeywordEditButton
            .addSelectionListener(new SelectionListener() {
               @Override
               public void widgetSelected(final SelectionEvent e) {
                  final IUserDefinedKeyword keyword = JMLProfileDialog.this
                        .getSelectedDerivedKeyword();
                  if (keyword == null) {
                     return;
                  }
                  final JMLKeywordDialog dialog = new JMLKeywordDialog(
                        JMLProfileDialog.this.getShell(),
                        JMLProfileDialog.this.derivedProfile, keyword);
                  dialog.open();
                  JMLProfileDialog.this.fillDerivedTable();
               }

               @Override
               public void widgetDefaultSelected(final SelectionEvent e) {
               }
            });

      this.derivedKeywordRemoveButton = this.createTableSideButton(myComposite,
            "Remove...");
      this.derivedKeywordRemoveButton
            .addSelectionListener(new SelectionListener() {
               @Override
               public void widgetSelected(final SelectionEvent e) {
                  final IUserDefinedKeyword keyword = JMLProfileDialog.this
                        .getSelectedDerivedKeyword();
                  if (keyword == null) {
                     return;
                  }
                  final boolean remove = MessageDialog.openConfirm(
                        JMLProfileDialog.this.getShell(), "Remove Keyword",
                        "Are you reall sure to remove the keyword \""
                              + keyword.getKeywords().iterator().next()
                              + "\"? \r\n(Cannot be undone!)");
                  if (remove) {
                     JMLProfileDialog.this.derivedProfile
                           .removeKeyword(keyword);
                     JMLProfileDialog.this.fillDerivedTable();
                  }
               }

               @Override
               public void widgetDefaultSelected(final SelectionEvent e) {
               }
            });
   }

   private void addDerivedTable(final Composite myComposite) {
      GridData data;
      data = new GridData(SWT.FILL, SWT.TOP, true, true);
      data.heightHint = 200;
      data.horizontalSpan = 2;
      data.verticalSpan = 3;

      this.derivedTable = new Table(myComposite, SWT.H_SCROLL | SWT.V_SCROLL
            | SWT.BORDER | SWT.FULL_SELECTION);
      this.derivedTable.setLayoutData(data);
      this.derivedTable.setHeaderVisible(true);
      this.derivedTable.setLinesVisible(true);

      this.derivedTable.addSelectionListener(new SelectionListener() {
         @Override
         public void widgetSelected(final SelectionEvent e) {
            JMLProfileDialog.this.derivedKeywordEditButton.setVisible(true);
            JMLProfileDialog.this.derivedKeywordRemoveButton.setVisible(true);
         }

         @Override
         public void widgetDefaultSelected(final SelectionEvent e) {
         }
      });

      final TableColumn genericKeywordTableColumn = new TableColumn(
            this.derivedTable, SWT.LEFT);
      genericKeywordTableColumn.setText("Keyword");
      genericKeywordTableColumn.setWidth(130);

      final TableColumn genericContentTableColumn = new TableColumn(
            this.derivedTable, SWT.LEFT);
      genericContentTableColumn.setText("Content");
      genericContentTableColumn.setWidth(165);

      final TableColumn genericDescriptionTableColumn = new TableColumn(
            this.derivedTable, SWT.LEFT);
      genericDescriptionTableColumn.setText("Description");
      genericDescriptionTableColumn.setWidth(165);

   }

   private void fillDerivedTable() {
      if (this.derivedTable == null) {
         return;
      }

      this.derivedTable.removeAll();
      final List<IKeyword> keywordList = new ArrayList<IKeyword>(
            this.derivedProfile.getAdditionalKeywords());

      Collections.sort(keywordList, this.keywordComparator);
      for (final IKeyword keyword : keywordList) {
         final TableItem item = new TableItem(this.derivedTable, 0);
         item.setText(this
               .keywordToDerivedTableData((IUserDefinedKeyword) keyword));
         item.setData(keyword);
      }

      this.derivedKeywordEditButton.setVisible(false);
      this.derivedKeywordRemoveButton.setVisible(false);

      this.derivedTable.setEnabled(true);
      this.derivedTable.redraw();
   }

   private String[] keywordToDerivedTableData(final IUserDefinedKeyword keyword) {
      String sourceDescription = keyword.getDescription();
      if (sourceDescription != null && sourceDescription.length() > 200) {
         sourceDescription = sourceDescription.substring(0, 196);
         sourceDescription += " ...";
         sourceDescription = sourceDescription.replace('\n', ' ');
      }
      final Iterator<String> iterator = keyword.getKeywords().iterator();
      String keywordString = iterator.next();
      while (iterator.hasNext()) {
         keywordString = keywordString + ", " + iterator.next();
      }

      final String content = keyword.getContentDescription().getDescription();

      return new String[] { keywordString, content, sourceDescription };
   }

   private IUserDefinedKeyword getSelectedDerivedKeyword() {
      final TableItem selectedItem = this.getSelectedDerivedTableItem();
      if (selectedItem == null) {
         System.out.println("noKeyword...");
         return null;
      }
      return (IUserDefinedKeyword) selectedItem.getData();
   }

   private int getComboIndexForProfile(final IJMLProfile profile) {
      for (int i = 0; i < this.derivedFromCombo.getItemCount(); i++) {
         if (this.derivedFromCombo.getItems()[i].equals(profile.getName())) {
            return i;
         }
      }
      return 0;
   }

   private TableItem getSelectedDerivedTableItem() {
      if (this.derivedTable.getSelection().length == 0) {
         System.out.println("noItem...");
         return null;
      }
      return this.derivedTable.getSelection()[0];
   }

   private IJMLProfile getSelectedProfileFromCombo() {
      final int index = this.derivedFromCombo.getSelectionIndex();
      if (index == -1) {
         return null;
      }
      return (IJMLProfile) this.derivedFromCombo.getData(this.derivedFromCombo
            .getItem(index));
   }

   /**
    * save the edited profile.
    *
    * @param onOkPressed
    * @return whether validation had success
    */
   private boolean saveEditProfile(final boolean onOkPressed) {
      System.out.println("saveEditProfile(" + onOkPressed + ")");
      final String profileName = this.profileNameText.getText();

      if (!profileName.equals(this.derivedProfile.getName())
            && !this.isProfileNameUnique(profileName)) {
         this.setMessage(NAME_EXISTS, IMessageProvider.ERROR);
         return false;
      }
      this.derivedProfile.setName(profileName);

      if (onOkPressed) {
         try {
            JMLProfileManagement.instance().writeDerivedProfiles();
         }
         catch (final InvalidProfileException ipe) {
            ipe.printStackTrace();
            return false;
         }
      }
      return true;
   }

   /**
    * create a new derived profile and save it.
    *
    * @param onOkPressed
    *           is this method called out of "okPressed"?
    * @return whether validation had success
    */
   private boolean saveNewProfile(final boolean onOkPressed) {
      System.out.println("saveNewProfile(" + onOkPressed + ")");
      final String profileName = this.profileNameText.getText();
      final String profileId = this.generateId(profileName);
      final IJMLProfile parentProfile = this.getSelectedProfileFromCombo();

      if (profileName.isEmpty()) {
         this.setMessage(PLEASE_FILL, IMessageProvider.ERROR);
         this.derivedProfile = null;
         return false;
      }
      if (parentProfile == null) {
         this.setMessage(PLEASE_SELECT, IMessageProvider.ERROR);
         this.derivedProfile = null;
         return false;
      }
      if (!this.isProfileNameUnique(profileName)) {
         this.setMessage(NAME_EXISTS, IMessageProvider.ERROR);
         this.derivedProfile = null;
         return false;
      }
      this.setMessage("", IMessageProvider.NONE);

      if (this.derivedProfile == null) {
         this.derivedProfile = parentProfile.derive(profileId, profileName);
      }

      if (onOkPressed) {
         try {
            JMLProfileManagement.instance().addUserDefinedProfile(
                  this.derivedProfile);
            JMLProfileManagement.instance().writeDerivedProfiles();
         }
         catch (final InvalidProfileException ipe) {
            ipe.printStackTrace();
            return false;
         }
      }
      return true;
   }

   @Override
   protected void okPressed() {
      boolean ok = true;
      System.out.println("profile == " + this.profile);
      System.out.println("derivedProfile == " + this.derivedProfile);
      if (this.profile == null) {
         ok = this.saveNewProfile(true);
      }
      else if (this.derivedProfile != null) {
         ok = this.saveEditProfile(true);
      }

      if (ok) {
         this.triggerRebuild();
         super.okPressed();
      }
   }

   private void triggerRebuild() {
      if (this.derivedProfile == null) {
         return;
      }
      final Set<IProject> affectedProjects = JMLProfileHelper
            .getProjectsUsingProfile(this.derivedProfile);
      final Runnable preferencesUpdater = new Runnable() {
         @Override
         public void run() {
            // write on derived Profiles already called;
         }
      };
      RebuildHelper.triggerRebuild(affectedProjects, this.getShell(),
            UserMessage.PROFILE_EDITED, preferencesUpdater);
   }
}