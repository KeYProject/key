package org.key_project.jmlediting.ui.preferencepages.profileDialog;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;

import org.eclipse.swt.SWT;
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
import org.key_project.jmlediting.ui.util.JMLSWTUtil;

public class JMLProfileEditDialog extends AbstractJMLProfileDialog {

   private IEditableDerivedProfile derivedProfile;

   private final Color redColor = Display.getCurrent().getSystemColor(
         SWT.COLOR_RED);
   private final Color greenColor = Display.getCurrent().getSystemColor(
         SWT.COLOR_DARK_GREEN);

   private static final String BUTTON_TEXT_DISABLE = "Disable";
   private static final String BUTTON_TEXT_ENABLE = "Enable";

   private Button enableDisableButton;
   private Text profileNameText;
   private Text profileIdText;
   private Combo derivedFromCombo;
   private Table derivedTable;

   public JMLProfileEditDialog(final Shell parent, final IJMLProfile profile) {
      super(parent, profile);
      this.setTitle("JML Profile Editor");
   }

   @Override
   protected Control createDialogArea(final Composite parent) {
      final Composite composite = (Composite) super.createDialogArea(parent);

      final GridData data = new GridData(SWT.FILL, SWT.FILL, true, true);
      final Composite myComposite = new Composite(composite, SWT.NONE);
      myComposite.setLayoutData(data);
      myComposite.setLayout(new GridLayout(3, false));

      this.addProfileName(myComposite);

      this.addProfileId(myComposite);

      this.addDerivedFrom(myComposite);

      this.addParentTableLabel(myComposite);

      this.addParentTable(myComposite);

      this.addEnableDisableButton(myComposite);

      this.addDerivedTableLabel(myComposite);

      this.addDerivedTable(myComposite);

      this.addDerivedButtons(myComposite);

      if (super.getProfileToEdit() != null) {
         this.setProfile(super.getProfileToEdit());
      }

      return composite;
   }

   private void addDerivedButtons(final Composite myComposite) {
      final Button derivedKeywordNewButton = this.createTableSideButton(
            myComposite, "New...");
      derivedKeywordNewButton.addSelectionListener(new SelectionListener() {
         @Override
         public void widgetSelected(final SelectionEvent e) {
            // TODO
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
            // TODO
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
            final TableItem selectedItem = JMLProfileEditDialog.this
                  .getSelectedParentTableItem();
            final IKeyword selectedKeyword = JMLProfileEditDialog.this
                  .getSelectedParentKeyword();
            if (JMLProfileEditDialog.this.derivedProfile
                  .isParentKeywordDisabled(selectedKeyword)) {
               JMLProfileEditDialog.this.enableDisableButton
                     .setText(BUTTON_TEXT_DISABLE);
               JMLProfileEditDialog.this.derivedProfile
                     .setParentKeywordDisabled(selectedKeyword, false);
               selectedItem.setForeground(JMLProfileEditDialog.this.greenColor);
            }
            else {
               JMLProfileEditDialog.this.enableDisableButton
                     .setText(BUTTON_TEXT_ENABLE);
               JMLProfileEditDialog.this.derivedProfile
                     .setParentKeywordDisabled(selectedKeyword, true);
               selectedItem.setForeground(JMLProfileEditDialog.this.redColor);
            }
         }

         @Override
         public void widgetDefaultSelected(final SelectionEvent e) {
         }
      });
   }

   private void addParentTable(final Composite myComposite) {
      GridData data;
      data = new GridData(SWT.FILL, SWT.TOP, true, true);
      data.heightHint = 200;
      data.horizontalSpan = 2;
      super.setKeywordTable(new Table(myComposite, SWT.H_SCROLL | SWT.V_SCROLL
            | SWT.BORDER | SWT.FULL_SELECTION));
      super.getKeywordTable().setLayoutData(data);
      super.getKeywordTable().setHeaderVisible(true);
      super.getKeywordTable().setLinesVisible(true);

      super.getKeywordTable().addSelectionListener(new SelectionListener() {
         @Override
         public void widgetSelected(final SelectionEvent e) {
            final IKeyword selectedKeyword = JMLProfileEditDialog.this
                  .getSelectedParentKeyword();
            if (JMLProfileEditDialog.this.derivedProfile
                  .isParentKeywordDisabled(selectedKeyword)) {
               JMLProfileEditDialog.this.enableDisableButton
                     .setText(BUTTON_TEXT_ENABLE);
            }
            else {
               JMLProfileEditDialog.this.enableDisableButton
                     .setText(BUTTON_TEXT_DISABLE);
            }
         }

         @Override
         public void widgetDefaultSelected(final SelectionEvent e) {
         }
      });

      final TableColumn genericKeywordTableColumn = new TableColumn(
            super.getKeywordTable(), SWT.LEFT);
      genericKeywordTableColumn.setText("Keyword");
      genericKeywordTableColumn.setWidth(150);

      final TableColumn genericDescriptionTableColumn = new TableColumn(
            super.getKeywordTable(), SWT.LEFT);
      genericDescriptionTableColumn.setText("Description");
      genericDescriptionTableColumn.setWidth(300);
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
      genericKeywordTableColumn.setWidth(150);

      final TableColumn genericDescriptionTableColumn = new TableColumn(
            this.derivedTable, SWT.LEFT);
      genericDescriptionTableColumn.setText("Description");
      genericDescriptionTableColumn.setWidth(300);
   }

   private void addParentTableLabel(final Composite myComposite) {
      GridData data;
      data = new GridData(SWT.LEFT, SWT.TOP, false, false, 1, 1);
      data.horizontalSpan = 3;
      data.verticalIndent = 20;
      final Label parentTableLabel = new Label(myComposite, SWT.NONE);
      parentTableLabel
            .setText("Keywords from parent profile: (Green: enabled; Red: disabled)");
      parentTableLabel.setLayoutData(data);
   }

   private void addDerivedTableLabel(final Composite myComposite) {
      GridData data;
      data = new GridData(SWT.LEFT, SWT.TOP, false, false, 1, 1);
      data.horizontalSpan = 3;
      data.verticalIndent = 20;
      final Label derivedTableLabel = new Label(myComposite, SWT.NONE);
      derivedTableLabel.setText("Custom Keywords: ");
      derivedTableLabel.setLayoutData(data);
   }

   private void addDerivedFrom(final Composite myComposite) {
      GridData data;
      data = new GridData(SWT.FILL, SWT.TOP, false, true);
      data.horizontalSpan = 1;
      final Label derivedFromLabel = new Label(myComposite, SWT.NONE);
      derivedFromLabel.setText("Derived from: ");
      derivedFromLabel.setLayoutData(data);

      data = new GridData(SWT.LEFT, SWT.TOP, true, true);
      data.horizontalSpan = 2;
      data.widthHint = 200;
      this.derivedFromCombo = new Combo(myComposite, SWT.BORDER | SWT.READ_ONLY);
      this.derivedFromCombo.setLayoutData(data);
      this.derivedFromCombo.setItems(JMLSWTUtil.getProfiles4Combo());
   }

   private void addProfileId(final Composite myComposite) {
      GridData data;
      data = new GridData(SWT.FILL, SWT.TOP, false, true);
      data.horizontalSpan = 1;
      final Label profileIdLabel = new Label(myComposite, SWT.NONE);
      profileIdLabel.setText("Profile ID: ");
      profileIdLabel.setLayoutData(data);

      data = new GridData(SWT.LEFT, SWT.TOP, true, true);
      data.horizontalSpan = 2;
      data.widthHint = 200;
      this.profileIdText = new Text(myComposite, SWT.SINGLE | SWT.BORDER);
      this.profileIdText.setLayoutData(data);
      this.profileIdText.setEnabled(false);
   }

   private void addProfileName(final Composite myComposite) {
      GridData data;
      data = new GridData(SWT.FILL, SWT.TOP, false, true);
      data.horizontalSpan = 1;
      final Label profileNameLabel = new Label(myComposite, SWT.NONE);
      profileNameLabel.setText("ProfileName: ");
      profileNameLabel.setLayoutData(data);

      data = new GridData(SWT.LEFT, SWT.TOP, true, true);
      data.horizontalSpan = 2;
      data.widthHint = 200;
      this.profileNameText = new Text(myComposite, SWT.SINGLE | SWT.BORDER);
      this.profileNameText.setLayoutData(data);
   }

   @Override
   public void setProfile(final IJMLProfile profile) {
      super.setProfileToEdit(profile);
      this.derivedProfile = (IEditableDerivedProfile) profile;

      if (super.getKeywordTable() == null) {
         return;
      }

      this.profileNameText.setText(profile.getName());
      this.profileIdText.setText(profile.getIdentifier());
      this.derivedFromCombo.select(this
            .getComboIndexForProfile(this.derivedProfile.getParentProfile()));
      this.derivedFromCombo.setEnabled(false);

      final Comparator<IKeyword> keywordComparator = new Comparator<IKeyword>() {
         @Override
         public int compare(final IKeyword o1, final IKeyword o2) {
            return o1.getKeywords().iterator().next()
                  .compareTo(o2.getKeywords().iterator().next());
         }
      };

      super.getKeywordTable().removeAll();
      final List<IKeyword> parentKeywordList = new ArrayList<IKeyword>(
            this.derivedProfile.getParentProfile().getSupportedKeywords());
      Collections.sort(parentKeywordList, keywordComparator);
      for (final IKeyword keyword : parentKeywordList) {
         final TableItem item = new TableItem(super.getKeywordTable(), SWT.NONE);
         item.setText(super.keywordToTableData(keyword));
         item.setData(keyword);
         if (this.derivedProfile.isParentKeywordDisabled(keyword)) {
            item.setForeground(this.redColor);
         }
         else {
            item.setForeground(this.greenColor);
         }
      }
      super.getKeywordTable().setEnabled(true);
      super.getKeywordTable().redraw();

      this.derivedTable.removeAll();
      final List<IKeyword> derivedKeywordList = new ArrayList<IKeyword>(
            this.derivedProfile.getAdditionalKeywords());
      Collections.sort(derivedKeywordList, keywordComparator);
      for (final IKeyword keyword : derivedKeywordList) {
         final TableItem item = new TableItem(this.derivedTable, SWT.NONE);
         item.setText(super.keywordToTableData(keyword));
         item.setData(keyword);
      }
      this.derivedTable.setEnabled(true);
      this.derivedTable.redraw();
   }

   private TableItem getSelectedParentTableItem() {
      return JMLProfileEditDialog.this.getKeywordTable().getSelection()[0];
   }

   private IKeyword getSelectedParentKeyword() {
      final TableItem selectedItem = this.getSelectedParentTableItem();
      return (IKeyword) selectedItem.getData();
   }

   private TableItem getSelectedDerivedTableItem() {
      return this.derivedTable.getSelection()[0];
   }

   private IKeyword getSelectedDerivedKeyword() {
      final TableItem selectedItem = this.getSelectedDerivedTableItem();
      return (IKeyword) selectedItem.getData();
   }

   private int getComboIndexForProfile(final IJMLProfile profile) {
      for (int i = 0; i < this.derivedFromCombo.getItemCount(); i++) {
         if (this.derivedFromCombo.getItems()[i].equals(profile.getName())) {
            return i;
         }
      }
      return 0;
   }

   @Override
   protected void okPressed() {
      this.derivedProfile.setName(this.profileNameText.getText());

      try {
         JMLProfileManagement.instance().writeDerivedProfiles();
      }
      catch (final InvalidProfileException ipe) {
         ipe.printStackTrace();
         return;
      }

      super.okPressed();
   }
}
