package org.key_project.jmlediting.ui.preferencepages.profileDialog;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

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
import org.key_project.jmlediting.core.profile.IDerivedProfile;
import org.key_project.jmlediting.core.profile.IEditableDerivedProfile;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLProfileManagement;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;

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

   public JMLProfileEditDialog(final Shell parent, final IJMLProfile profile) {
      super(parent, profile);
      this.setTitle("JML Profile Editor");
   }

   @Override
   protected Control createDialogArea(final Composite parent) {
      final Composite composite = (Composite) super.createDialogArea(parent);

      GridData data = new GridData(SWT.FILL, SWT.FILL, true, true);
      final Composite myComposite = new Composite(composite, SWT.NONE);
      myComposite.setLayoutData(data);
      myComposite.setLayout(new GridLayout(3, false));

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
      this.derivedFromCombo.setItems(this.getProfiles4Combo());

      data = new GridData(SWT.LEFT, SWT.TOP, false, false, 1, 1);
      data.horizontalSpan = 3;
      data.verticalIndent = 20;
      final Label parentTableLabel = new Label(myComposite, SWT.NONE);
      parentTableLabel
            .setText("Keywords from parent profile: (Green: enabled; Red: disabled)");
      parentTableLabel.setLayoutData(data);

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
                  .getSelectedKeyword();
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

      this.enableDisableButton = this.createTableSideButton(myComposite,
            "En/Disable");
      this.enableDisableButton.addSelectionListener(new SelectionListener() {
         @Override
         public void widgetSelected(final SelectionEvent e) {
            final TableItem selectedItem = JMLProfileEditDialog.this
                  .getSelectedTableItem();
            final IKeyword selectedKeyword = JMLProfileEditDialog.this
                  .getSelectedKeyword();
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

      if (super.getProfileToEdit() != null) {
         this.setProfile(super.getProfileToEdit());
      }

      return composite;
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

      super.getKeywordTable().removeAll();
      final List<IKeyword> keywordList = new ArrayList<IKeyword>(
            this.derivedProfile.getParentProfile().getSupportedKeywords());
      Collections.sort(keywordList, new Comparator<IKeyword>() {
         @Override
         public int compare(final IKeyword o1, final IKeyword o2) {
            return o1.getKeywords().iterator().next()
                  .compareTo(o2.getKeywords().iterator().next());
         }
      });
      for (final IKeyword keyword : keywordList) {
         final TableItem item = new TableItem(super.getKeywordTable(), 0);
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
   }

   private TableItem getSelectedTableItem() {
      return JMLProfileEditDialog.this.getKeywordTable().getSelection()[0];
   }

   private IKeyword getSelectedKeyword() {
      final TableItem selectedItem = this.getSelectedTableItem();
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

   private String[] getProfiles4Combo() {
      final Set<IJMLProfile> allProfiles = JMLProfileManagement.instance()
            .getAvailableProfiles();

      final StringBuilder resultBuilder = new StringBuilder();

      final Iterator<IJMLProfile> iterator = allProfiles.iterator();
      while (iterator.hasNext()) {
         final IJMLProfile profile = iterator.next();
         if (!(profile instanceof IDerivedProfile)) {
            resultBuilder.append(profile.getName() + ";");
         }
      }

      resultBuilder.deleteCharAt(resultBuilder.length() - 1);

      final String[] result = resultBuilder.toString().split(";");

      Arrays.sort(result);

      return result;
   }
}
