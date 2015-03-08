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
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;
import org.eclipse.swt.widgets.TableItem;
import org.key_project.jmlediting.core.profile.IEditableDerivedProfile;
import org.key_project.jmlediting.core.profile.IJMLProfile;
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
      myComposite.setLayout(new GridLayout(2, false));

      data = new GridData(SWT.LEFT, SWT.TOP, false, false, 1, 1);
      data.horizontalSpan = 2;
      final Label label = new Label(myComposite, SWT.NONE);
      label.setText("Keywords from parent profile: (Green: enabled; Red: disabled)");
      label.setLayoutData(data);

      data = new GridData(SWT.FILL, SWT.TOP, true, true);
      data.heightHint = 200;

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
}
