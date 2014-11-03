package org.key_project.jmlediting.ui;

import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.List;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.IWorkbenchPropertyPage;
import org.eclipse.ui.dialogs.PropertyPage;

public class JMLProfilePropertiesPage extends PropertyPage implements
      IWorkbenchPropertyPage {

   private Button useDefaultButton;
   private List profilesList;
   
   public JMLProfilePropertiesPage() {
      // TODO Auto-generated constructor stub
   }

   @Override
   protected Control createContents(Composite parent) {
      final Composite myComposite = new Composite(parent, SWT.NONE);
      final GridLayout layout = new GridLayout();
      layout.numColumns=1;
      myComposite.setLayout(layout);
      
      GridData data = new GridData();
      data.grabExcessHorizontalSpace = true;
      
      this.useDefaultButton = new Button(myComposite, SWT.CHECK);
      this.useDefaultButton.setText("Use project specific settings");
      this.useDefaultButton.setData(data);
      
      data = new GridData();
      data.grabExcessHorizontalSpace = true;
      data.grabExcessVerticalSpace = true;
      
      this.profilesList = new List(myComposite, SWT.V_SCROLL| SWT.SINGLE |SWT.BORDER);
      this.profilesList.setData(data);
      
      return myComposite;
   }

}
