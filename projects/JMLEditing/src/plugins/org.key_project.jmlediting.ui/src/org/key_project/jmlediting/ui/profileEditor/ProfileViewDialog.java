package org.key_project.jmlediting.ui.profileEditor;

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
import org.key_project.jmlediting.core.profile.syntax.ISpecificationStatementKeyword;

public class ProfileViewDialog extends StatusDialog {
   
   
   private IJMLProfile profileToEdit;
   
   
   private Table supportedGenericSpecifications;
   private TableColumn genericKeywordTableColumn;
   private TableColumn genericDescriptionTableColumn;


   public ProfileViewDialog(Shell parent) {
      super(parent);
      this.setTitle("JML Profile Editor");
      this.setShellStyle(super.getShellStyle() | SWT.RESIZE);
   }
   
   @Override
   protected Control createDialogArea(Composite parent) {
      final Composite composite = (Composite) super.createDialogArea(parent);
      
      Composite myComposite= new Composite(composite, SWT.NONE);
      myComposite.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, false));
      myComposite.setLayout(new GridLayout(1, false));
      
      Label label = new Label(myComposite, SWT.NONE);
      label.setText("Supported generic specifications");
      label.setLayoutData(new GridData(SWT.LEFT, SWT.TOP, false, false, 1, 1));
      
      GridData data = new GridData(SWT.LEFT, SWT.TOP, true, false, 1, 1);
      data.horizontalAlignment = SWT.FILL;
      
      this.supportedGenericSpecifications = new Table(myComposite, SWT.SINGLE | SWT.FULL_SELECTION | SWT.BORDER);
      this.supportedGenericSpecifications.setLayoutData(data);
      this.supportedGenericSpecifications.setHeaderVisible(true);
      this.supportedGenericSpecifications.setLinesVisible(true);
      
      this.genericKeywordTableColumn = new TableColumn(this.supportedGenericSpecifications, SWT.LEFT);
      this.genericKeywordTableColumn.setText("Keyword");
      this.genericKeywordTableColumn.setWidth(100);

      this.genericDescriptionTableColumn = new TableColumn(this.supportedGenericSpecifications, SWT.LEFT);
      this.genericDescriptionTableColumn.setText("Description");
      this.genericDescriptionTableColumn.setWidth(200);
      
      if (this.profileToEdit != null) {
         this.setProfile(this.profileToEdit);
      }
      
      return composite;
   }
   
   public void setProfile(IJMLProfile profile) {
      
      this.profileToEdit = profile;
      
      if (this.supportedGenericSpecifications == null) {
         return;
      }
     
      this.supportedGenericSpecifications.removeAll();
      
      for (ISpecificationStatementKeyword gSpec : this.profileToEdit.getSupportedSpecificationStatementKeywords()) {
        TableItem item = new TableItem(this.supportedGenericSpecifications, 0);
        item.setText(gSpecToTableData(gSpec));
      }
      
      
   }
   
   private String[] gSpecToTableData(ISpecificationStatementKeyword gSpec) {
      String sourceDescription = gSpec.getDescription();
      if (sourceDescription.length() > 200) {
         sourceDescription = sourceDescription.substring(0, 196);
         sourceDescription += " ...";
      }
      String cleanedDescription = sourceDescription.replace('\n', ' ');
      return new String[] {gSpec.getKeyword(), cleanedDescription};
   }

}
