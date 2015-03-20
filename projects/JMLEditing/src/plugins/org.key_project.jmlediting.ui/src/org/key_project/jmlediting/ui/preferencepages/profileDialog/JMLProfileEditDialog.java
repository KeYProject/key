package org.key_project.jmlediting.ui.preferencepages.profileDialog;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.Iterator;
import java.util.List;

import org.eclipse.jface.dialogs.IMessageProvider;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;
import org.eclipse.swt.widgets.TableItem;
import org.key_project.jmlediting.core.profile.IEditableDerivedProfile;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.InvalidProfileException;
import org.key_project.jmlediting.core.profile.JMLProfileManagement;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.core.profile.syntax.user.IUserDefinedKeyword;

public class JMLProfileEditDialog extends AbstractJMLProfileDialog {

   private IEditableDerivedProfile derivedProfile;

   private final Color redColor = Display.getCurrent().getSystemColor(
         SWT.COLOR_RED);
   private final Color greenColor = Display.getCurrent().getSystemColor(
         SWT.COLOR_DARK_GREEN);

   private static final String BUTTON_TEXT_DISABLE = "Disable";
   private static final String BUTTON_TEXT_ENABLE = "Enable";

   private Button enableDisableButton;
   private Table derivedTable;

   public JMLProfileEditDialog(final Shell parent, final IJMLProfile profile) {
      super(parent, profile, "JML Profile Editor", "Profile ID: "
            + profile.getIdentifier());
   }

   @Override
   protected Control getDialogArea(final Composite composite) {
      final GridData data = new GridData(SWT.FILL, SWT.FILL, true, true);
      final Composite myComposite = new Composite(composite, SWT.NONE);
      myComposite.setLayoutData(data);
      myComposite.setLayout(this.getLayout());

      super.addProfileName(myComposite, true);

      super.addDerivedFrom(myComposite, false);

      super.addKeywordTableLabel(myComposite,
            "Keywords from parent profile: (Green: enabled; Red: disabled)");

      super.addKeywordTable(myComposite, 200);
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

      this.addEnableDisableButton(myComposite);

      this.addDerivedTableLabel(myComposite);

      this.addDerivedTable(myComposite);

      this.addDerivedButtons(myComposite);

      return composite;
   }

   private void addDerivedButtons(final Composite myComposite) {
      final Button derivedKeywordNewButton = this.createTableSideButton(
            myComposite, "New...");
      derivedKeywordNewButton.addSelectionListener(new SelectionListener() {
         @Override
         public void widgetSelected(final SelectionEvent e) {
            final JMLKeywordDialog dialog = new JMLKeywordDialog(
                  JMLProfileEditDialog.this.getShell(),
                  JMLProfileEditDialog.this.derivedProfile, null);
            dialog.open();
            JMLProfileEditDialog.this.fillDerivedTable();
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
            final IUserDefinedKeyword keyword = JMLProfileEditDialog.this
                  .getSelectedDerivedKeyword();
            if (keyword == null) {
               System.out.println("keyword == null?!?!");
               return;
            }
            final JMLKeywordDialog dialog = new JMLKeywordDialog(
                  JMLProfileEditDialog.this.getShell(),
                  JMLProfileEditDialog.this.derivedProfile, keyword);
            dialog.open();
            JMLProfileEditDialog.this.fillDerivedTable();
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

   @Override
   public void setProfile(final IJMLProfile profile) {
      super.setProfile(profile);

      this.profileNameText.setText(profile.getName());
      this.fillDerivedTable();
   }

   @Override
   protected void fillKeywordTable() {
      this.derivedProfile = (IEditableDerivedProfile) this.getProfileToEdit();

      if (super.getKeywordTable() == null) {
         return;
      }

      this.derivedFromCombo.select(this
            .getComboIndexForProfile(this.derivedProfile.getParentProfile()));

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
   };

   private void fillDerivedTable() {
      if (this.derivedTable == null) {
         return;
      }

      this.derivedTable.removeAll();
      final List<IKeyword> keywordList = new ArrayList<IKeyword>(
            this.derivedProfile.getAdditionalKeywords());

      Collections.sort(keywordList, new Comparator<IKeyword>() {
         @Override
         public int compare(final IKeyword o1, final IKeyword o2) {
            return o1.getKeywords().iterator().next()
                  .compareTo(o2.getKeywords().iterator().next());
         }
      });
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

   @Override
   protected void okPressed() {
      final String profileName = this.profileNameText.getText();

      if (!profileName.equals(this.derivedProfile.getName())
            && !this.checkProfileNameUnique(profileName)) {
         this.setMessage(this.NAME_EXISTS, IMessageProvider.ERROR);
         return;
      }
      this.derivedProfile.setName(profileName);

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
