package org.key_project.sed.ui.wizard.page;

import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.annotation.ISEDAnnotationType;
import org.key_project.sed.ui.composite.AnnotationAppearanceComposite;
import org.key_project.util.java.StringUtil;

/**
 * This {@link WizardPage} defines search criteria.
 * @author Martin Hentschel
 */
public class SearchWizardPage extends WizardPage {
   /**
    * The {@link ISEDAnnotationType} from which the search annotation will be created.
    */
   private final ISEDAnnotationType annotationType;
   
   /**
    * Defines the search text.
    */
   private Text searchText;
   
   /**
    * The used {@link AnnotationAppearanceComposite}.
    */
   private AnnotationAppearanceComposite annotationAppearanceComposite;
   
   /**
    * Constructor.
    * @param pageName The name of this {@link WizardPage}.
    * @param annotationType The {@link ISEDAnnotationType} from which the search annotation will be created.
    */
   public SearchWizardPage(String pageName, ISEDAnnotationType annotationType) {
      super(pageName);
      this.annotationType = annotationType;
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
      root.setLayout(new GridLayout(1, false));
      Group searchGroup = new Group(root, SWT.NONE);
      searchGroup.setText("Search");
      searchGroup.setLayout(new GridLayout(2, false));
      searchGroup.setLayoutData(new GridData(GridData.FILL_BOTH));
      Label searchLabel = new Label(searchGroup, SWT.NONE);
      searchLabel.setLayoutData(new GridData(SWT.LEFT, SWT.TOP, false, false));
      searchLabel.setText("&Text");
      searchText = new Text(searchGroup, SWT.BORDER | SWT.MULTI);
      searchText.setLayoutData(new GridData(GridData.FILL_BOTH));
      searchText.addModifyListener(new ModifyListener() {
         @Override
         public void modifyText(ModifyEvent e) {
            updatePageComplete();
         }
      });
      annotationAppearanceComposite = new AnnotationAppearanceComposite(root, SWT.NONE, annotationType);
      annotationAppearanceComposite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
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

   /**
    * Applies the appearance to the given {@link ISEDAnnotation}.
    * @param annotation The {@link ISEDAnnotation} to modify.
    */
   public void applyAppearance(ISEDAnnotation annotation) {
      annotationAppearanceComposite.applyChanges(annotation);
   }
}
