package org.key_project.sed.ui.wizard.page;

import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.key_project.util.java.StringUtil;

/**
 * This {@link WizardPage} defines search criteria.
 * @author Martin Hentschel
 */
public class SearchWizardPage extends WizardPage {
   /**
    * Defines the search text.
    */
   private Text searchText;
   
   /**
    * Constructor.
    * @param pageName The name of this {@link WizardPage}.
    */
   public SearchWizardPage(String pageName) {
      super(pageName);
      setTitle("Search");
      setDescription("Define search criteria");
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void createControl(Composite parent) {
      Composite root = new Composite(parent, SWT.NONE);
      setControl(root);
      root.setLayout(new GridLayout(2, false));
      Label searchLabel = new Label(root, SWT.NONE);
      searchLabel.setLayoutData(new GridData(SWT.LEFT, SWT.TOP, false, false));
      searchLabel.setText("&Text");
      searchText = new Text(root, SWT.BORDER | SWT.MULTI);
      searchText.setLayoutData(new GridData(GridData.FILL_BOTH));
      searchText.addModifyListener(new ModifyListener() {
         @Override
         public void modifyText(ModifyEvent e) {
            updatePageComplete();
         }
      });
      updatePageComplete();
   }
   
   /**
    * Updates the page complete state.
    */
   protected void updatePageComplete() {
      if (StringUtil.isTrimmedEmpty(getSearch())) {
         setPageComplete(false);
         setErrorMessage("No text defined.");
      }
      else {
         setPageComplete(true);
         setErrorMessage(null);
      }
   }
   
   /**
    * Returns the defined search.
    * @return The defined search.
    */
   public String getSearch() {
      return searchText.getText();
   }
}
