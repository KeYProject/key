package org.key_project.jmlediting.ui.preferencepages.profileEditor;

import org.eclipse.jface.dialogs.StatusDialog;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;
import org.eclipse.swt.widgets.TableItem;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;

public class ProfileEditorDialog extends StatusDialog {

   private IJMLProfile profileToEdit;

   private Table supportedGenericSpecifications;
   private TableColumn genericKeywordTableColumn;
   private TableColumn genericDescriptionTableColumn;

   private Button editButton;

   public ProfileEditorDialog(final Shell parent) {
      super(parent);
      this.setTitle("JML Profile Editor");
      this.setShellStyle(super.getShellStyle() | SWT.RESIZE);
   }

   @Override
   protected Control createDialogArea(final Composite parent) {
      final Composite composite = (Composite) super.createDialogArea(parent);

      final Composite myComposite = new Composite(composite, SWT.NONE);
      myComposite.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, false));
      myComposite.setLayout(new GridLayout(1, false));

      final Label label = new Label(myComposite, SWT.NONE);
      label.setText("Supported generic specifications");
      label.setLayoutData(new GridData(SWT.LEFT, SWT.TOP, false, false, 1, 1));

      GridData data = new GridData(SWT.LEFT, SWT.TOP, true, false, 1, 1);
      data.horizontalAlignment = SWT.FILL;

      this.supportedGenericSpecifications = new Table(myComposite, SWT.SINGLE
            | SWT.FULL_SELECTION | SWT.BORDER);
      this.supportedGenericSpecifications.setLayoutData(data);
      this.supportedGenericSpecifications.setHeaderVisible(true);
      this.supportedGenericSpecifications.setLinesVisible(true);

      this.genericKeywordTableColumn = new TableColumn(
            this.supportedGenericSpecifications, SWT.LEFT);
      this.genericKeywordTableColumn.setText("Keyword");
      this.genericKeywordTableColumn.setWidth(100);

      this.genericDescriptionTableColumn = new TableColumn(
            this.supportedGenericSpecifications, SWT.LEFT);
      this.genericDescriptionTableColumn.setText("Description");
      this.genericDescriptionTableColumn.setWidth(200);

      data = new GridData(SWT.RIGHT, SWT.TOP, false, false, 1, 1);
      this.editButton = new Button(myComposite, SWT.PUSH);
      this.editButton.setText(" Edit ... ");
      this.editButton.setLayoutData(data);

      if (this.profileToEdit != null) {
         this.setProfile(this.profileToEdit);
      }

      return composite;
   }

   public void setProfile(final IJMLProfile profile) {

      this.profileToEdit = profile;

      if (this.supportedGenericSpecifications == null) {
         return;
      }

      this.supportedGenericSpecifications.removeAll();

      for (final IKeyword gSpec : this.profileToEdit.getSupportedKeywords()) {
         final TableItem item = new TableItem(
               this.supportedGenericSpecifications, 0);
         item.setText(this.keywordToTableData(gSpec));
      }

      // TODO
      // final boolean editable = profile.isConfigurable() != null;
      this.supportedGenericSpecifications.setEnabled(true);
   }

   private String[] keywordToTableData(final IKeyword keyword) {
      String sourceDescription = keyword.getDescription();
      if (sourceDescription != null && sourceDescription.length() > 200) {
         sourceDescription = sourceDescription.substring(0, 196);
         sourceDescription += " ...";
         sourceDescription = sourceDescription.replace('\n', ' ');
      }
      return new String[] { keyword.getKeywords().toString(), sourceDescription };
   }

}
