package org.key_project.jmlediting.ui.preferencepages.profileDialog;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.Date;
import java.util.Iterator;
import java.util.List;
import java.util.Random;

import org.eclipse.jface.dialogs.IMessageProvider;
import org.eclipse.jface.dialogs.TitleAreaDialog;
import org.eclipse.jface.fieldassist.ControlDecoration;
import org.eclipse.jface.fieldassist.FieldDecorationRegistry;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;
import org.eclipse.swt.widgets.TableItem;
import org.eclipse.swt.widgets.Text;
import org.key_project.jmlediting.core.profile.IEditableDerivedProfile;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.InvalidProfileException;
import org.key_project.jmlediting.core.profile.JMLProfileManagement;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.core.profile.syntax.user.IUserDefinedKeyword;
import org.key_project.jmlediting.ui.util.JMLSWTUtil;

public class JMLProfileDialog extends TitleAreaDialog {
   private final String NAME_EXISTS = "Profile Name already exists!";
   private final String PLEASE_SELECT = "Please select a profile to derive from!";
   private final String PLEASE_FILL = "Profile Name must not be empty!";
   private final String BUTTON_TEXT_DISABLE = "Disable";
   private final String BUTTON_TEXT_ENABLE = "Enable";

   private final IJMLProfile profile;
   private IEditableDerivedProfile derivedProfile;

   private Table keywordTable;
   private Button enableDisableButton;
   private Table derivedTable;

   private final String title;
   private final String message;

   private Text profileNameText;
   private ControlDecoration profileNameError;
   private Combo derivedFromCombo;
   private ControlDecoration comboError;

   private final Comparator<IKeyword> keywordComparator = new Comparator<IKeyword>() {
      @Override
      public int compare(final IKeyword o1, final IKeyword o2) {
         return o1.getKeywords().iterator().next()
               .compareTo(o2.getKeywords().iterator().next());
      }
   };

   private final Color redColor = Display.getCurrent().getSystemColor(
         SWT.COLOR_RED);
   private final Color greenColor = Display.getCurrent().getSystemColor(
         SWT.COLOR_DARK_GREEN);

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

      this.addProfileName(myComposite, true);

      if (this.profile == null
            || (this.derivedProfile == null || this.derivedProfile instanceof IEditableDerivedProfile)) {
         this.addDerivedFrom(myComposite, this.derivedProfile == null);
         if (this.derivedProfile == null) {
            this.derivedFromCombo.addSelectionListener(new SelectionListener() {

               @Override
               public void widgetSelected(final SelectionEvent e) {
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

         this.addKeywordTableLabel(myComposite,
               "Keywords from parent profile: (Green: enabled; Red: disabled)");
         this.addKeywordTable(myComposite, 200);
         this.keywordTable.addSelectionListener(new SelectionListener() {
            @Override
            public void widgetSelected(final SelectionEvent e) {
               final IKeyword selectedKeyword = JMLProfileDialog.this
                     .getSelectedParentKeyword();
               if (JMLProfileDialog.this.derivedProfile == null
                     && !JMLProfileDialog.this.saveNewProfile(false)) {
                  return;
               }
               if (JMLProfileDialog.this.derivedProfile
                     .isParentKeywordDisabled(selectedKeyword)) {
                  JMLProfileDialog.this.enableDisableButton
                        .setText(JMLProfileDialog.this.BUTTON_TEXT_ENABLE);
               }
               else {
                  JMLProfileDialog.this.enableDisableButton
                        .setText(JMLProfileDialog.this.BUTTON_TEXT_DISABLE);
               }
            }

            @Override
            public void widgetDefaultSelected(final SelectionEvent e) {
            }
         });
         this.addEnableDisableButton(myComposite);

         this.addDerivedTableLabel(myComposite);

         this.addDerivedTable(myComposite);

         this.addDerivedButtons(myComposite);
      }
      else {
         this.profileNameText.setText(this.profile.getName());
         this.addKeywordTableLabel(myComposite, "Supported Keywords");

         this.addKeywordTable(myComposite, 400);
      }

      this.fillKeywordTable();
      if (this.profile != null
            && this.profile instanceof IEditableDerivedProfile) {
         this.derivedProfile = (IEditableDerivedProfile) this.profile;
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
      derivedFromLabel.setText("Derived from: ");
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
      this.comboError.setDescriptionText(this.PLEASE_SELECT);
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
      profileNameLabel.setText("ProfileName: ");
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
      this.profileNameError.setDescriptionText(this.PLEASE_FILL);
      this.profileNameError.show();

      this.profileNameText.addModifyListener(new ModifyListener() {
         @Override
         public void modifyText(final ModifyEvent e) {
            if (JMLProfileDialog.this.profileNameText.getText().isEmpty()) {
               JMLProfileDialog.this.profileNameError
                     .setDescriptionText(JMLProfileDialog.this.PLEASE_FILL);
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
      derivedTableLabel.setText("Custom Keywords: ");
      derivedTableLabel.setLayoutData(data);
   }

   private void addKeywordTable(final Composite myComposite, final int height) {
      GridData data;
      data = new GridData(SWT.FILL, SWT.TOP, true, true, 2, 1);
      data.heightHint = height;
      this.keywordTable = new Table(myComposite, SWT.H_SCROLL | SWT.V_SCROLL
            | SWT.BORDER | SWT.FULL_SELECTION);
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

   private IKeyword getSelectedParentKeyword() {
      final TableItem selectedItem = this.getSelectedParentTableItem();
      if (selectedItem == null) {
         return null;
      }
      return (IKeyword) selectedItem.getData();
   }

   private TableItem getSelectedParentTableItem() {
      if (this.keywordTable.getSelection().length == 0) {
         return null;
      }
      return this.keywordTable.getSelection()[0];
   }

   private void fillKeywordTable() {
      if (this.keywordTable == null) {
         return;
      }

      this.keywordTable.removeAll();

      final List<IKeyword> keywordList;
      if (this.derivedProfile != null) {
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
      else {
         return;
      }

      Collections.sort(keywordList, this.keywordComparator);
      for (final IKeyword keyword : keywordList) {
         final TableItem item = new TableItem(this.keywordTable, SWT.NONE);
         item.setText(this.keywordToTableData(keyword));
         item.setData(keyword);
         if (this.derivedProfile != null) {
            if (this.derivedProfile.isParentKeywordDisabled(keyword)) {
               item.setForeground(this.redColor);
            }
            else {
               item.setForeground(this.greenColor);
            }
         }
      }
      this.keywordTable.setEnabled(true);
      this.keywordTable.redraw();
   }

   private boolean checkProfileNameUnique(final String profileName) {
      if (JMLProfileManagement.instance().getProfileFromName(profileName) != null) {
         this.profileNameError.setDescriptionText(this.NAME_EXISTS);
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
      final Button derivedKeywordEditButton = this.createTableSideButton(
            myComposite, "Edit...");
      derivedKeywordEditButton.addSelectionListener(new SelectionListener() {
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
      final Button derivedKeywordRemoveButton = this.createTableSideButton(
            myComposite, "Remove...");
      derivedKeywordRemoveButton.addSelectionListener(new SelectionListener() {
         @Override
         public void widgetSelected(final SelectionEvent e) {
            // TODO
         }

         @Override
         public void widgetDefaultSelected(final SelectionEvent e) {
         }
      });
   }

   private void addEnableDisableButton(final Composite myComposite) {
      this.enableDisableButton = this.createTableSideButton(myComposite,
            "En/Disable");
      this.enableDisableButton.addSelectionListener(new SelectionListener() {
         @Override
         public void widgetSelected(final SelectionEvent e) {
            final TableItem selectedItem = JMLProfileDialog.this
                  .getSelectedParentTableItem();
            final IKeyword selectedKeyword = JMLProfileDialog.this
                  .getSelectedParentKeyword();

            if (JMLProfileDialog.this.derivedProfile == null
                  && !JMLProfileDialog.this.saveNewProfile(false)) {
               System.out.println("returning from enableDisableButton...");
               return;
            }

            if (JMLProfileDialog.this.derivedProfile
                  .isParentKeywordDisabled(selectedKeyword)) {
               JMLProfileDialog.this.enableDisableButton
                     .setText(JMLProfileDialog.this.BUTTON_TEXT_DISABLE);
               JMLProfileDialog.this.derivedProfile.setParentKeywordDisabled(
                     selectedKeyword, false);
               selectedItem.setForeground(JMLProfileDialog.this.greenColor);
            }
            else {
               JMLProfileDialog.this.enableDisableButton
                     .setText(JMLProfileDialog.this.BUTTON_TEXT_ENABLE);
               JMLProfileDialog.this.derivedProfile.setParentKeywordDisabled(
                     selectedKeyword, true);
               selectedItem.setForeground(JMLProfileDialog.this.redColor);
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
            // TODO
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

   private boolean saveEditProfile(final boolean onOkPressed) {
      System.out.println("saveEditProfile(" + onOkPressed + ")");
      final String profileName = this.profileNameText.getText();

      if (!profileName.equals(this.derivedProfile.getName())
            && !this.checkProfileNameUnique(profileName)) {
         this.setMessage(this.NAME_EXISTS, IMessageProvider.ERROR);
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

   private boolean saveNewProfile(final boolean onOkPressed) {
      System.out.println("saveNewProfile(" + onOkPressed + ")");
      final String profileName = this.profileNameText.getText();
      final String profileId = this.generateId(profileName);
      final IJMLProfile parentProfile = this.getSelectedProfileFromCombo();

      if (profileName.isEmpty()) {
         this.setMessage(this.PLEASE_FILL, IMessageProvider.ERROR);
         return false;
      }
      else if (parentProfile == null) {
         this.setMessage(this.PLEASE_SELECT, IMessageProvider.ERROR);
         return false;
      }
      else if (!this.checkProfileNameUnique(profileName)) {
         this.setMessage(this.NAME_EXISTS, IMessageProvider.ERROR);
         return false;
      }
      else {
         this.setMessage("", IMessageProvider.NONE);
      }

      final IEditableDerivedProfile newProfile = parentProfile.derive(
            profileId, profileName);

      if (onOkPressed) {
         try {
            JMLProfileManagement.instance().addUserDefinedProfile(newProfile);
            JMLProfileManagement.instance().writeDerivedProfiles();
         }
         catch (final InvalidProfileException ipe) {
            ipe.printStackTrace();
            return false;
         }
      }
      else {
         this.derivedProfile = newProfile;
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
         super.okPressed();
      }
   }
}