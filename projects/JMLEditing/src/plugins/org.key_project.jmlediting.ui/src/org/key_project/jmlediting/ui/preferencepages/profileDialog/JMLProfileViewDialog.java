package org.key_project.jmlediting.ui.preferencepages.profileDialog;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;

import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;
import org.eclipse.swt.widgets.TableItem;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;

public class JMLProfileViewDialog extends AbstractJMLProfileDialog {

   public JMLProfileViewDialog(final Shell parent, final IJMLProfile profile) {
      super(parent, profile);
      this.setTitle("JML Profile Viewer");
   }

   @Override
   public void setProfile(final IJMLProfile profile) {
      super.setProfileToEdit(profile);

      if (super.getKeywordTable() == null) {
         return;
      }

      super.getKeywordTable().removeAll();
      final List<IKeyword> keywordList = new ArrayList<IKeyword>(super
            .getProfileToEdit().getSupportedKeywords());

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
      }

      super.getKeywordTable().setEnabled(true);
      super.getKeywordTable().redraw();
   }

   @Override
   protected Control createDialogArea(final Composite parent) {
      final Composite composite = (Composite) super.createDialogArea(parent);

      GridData data = new GridData(SWT.FILL, SWT.FILL, true, true);

      final Composite myComposite = new Composite(composite, SWT.NONE);
      myComposite.setLayoutData(data);
      myComposite.setLayout(new GridLayout(1, false));

      data = new GridData(SWT.LEFT, SWT.TOP, false, false, 1, 1);
      final Label label = new Label(myComposite, SWT.NONE);
      label.setText("Supported Keywords");
      label.setLayoutData(data);

      data = new GridData(SWT.FILL, SWT.TOP, true, true);
      data.horizontalSpan = 1;
      data.verticalSpan = 1;
      data.heightHint = 400;

      super.setKeywordTable(new Table(myComposite, SWT.H_SCROLL | SWT.V_SCROLL
            | SWT.BORDER | SWT.FULL_SELECTION));
      super.getKeywordTable().setLayoutData(data);
      super.getKeywordTable().setHeaderVisible(true);
      super.getKeywordTable().setLinesVisible(true);

      final TableColumn genericKeywordTableColumn = new TableColumn(
            super.getKeywordTable(), SWT.LEFT);
      genericKeywordTableColumn.setText("Keyword");
      genericKeywordTableColumn.setWidth(150);

      final TableColumn genericDescriptionTableColumn = new TableColumn(
            super.getKeywordTable(), SWT.LEFT);
      genericDescriptionTableColumn.setText("Description");
      genericDescriptionTableColumn.setWidth(300);

      if (super.getProfileToEdit() != null) {
         this.setProfile(super.getProfileToEdit());
      }

      return composite;
   }
}
