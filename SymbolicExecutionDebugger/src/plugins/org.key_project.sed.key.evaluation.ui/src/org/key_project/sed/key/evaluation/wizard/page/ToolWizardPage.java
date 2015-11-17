package org.key_project.sed.key.evaluation.wizard.page;

import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.swt.browser.Browser;
import org.eclipse.swt.browser.LocationEvent;
import org.eclipse.swt.browser.LocationListener;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.key_project.sed.key.evaluation.model.definition.Tool;
import org.key_project.sed.key.evaluation.model.input.ToolPageInput;
import org.key_project.sed.key.evaluation.wizard.manager.BrowserManager;

public class ToolWizardPage extends AbstractEvaluationWizardPage<ToolPageInput> {
   public ToolWizardPage(ToolPageInput pageInput, ImageDescriptor imageDescriptor) {
      super(pageInput, imageDescriptor, true);
   }

   @Override
   protected void createContent(FormToolkit toolkit, Composite parent) {
      Browser browser = BrowserManager.createBrowser(toolkit, parent, getPageInput().getPage().getTool().getWizardDescriptionURL());
      browser.addLocationListener(new LocationListener() {
         @Override
         public void changing(LocationEvent event) {
            if (event.location != null &&
                event.location.endsWith("#performRunnable")) {
               getContainer().resetWorkbench();
            }
         }
         
         @Override
         public void changed(LocationEvent event) {
         }
      });
   }

   @Override
   protected void updatePageCompleted() {
      String errorMessage = getRunnablesFailure();
      setErrornousControl(null);
      setPageComplete(errorMessage == null);
      setErrorMessage(errorMessage);
   }

   @Override
   public boolean isPerformWorkbenchModifierAutomatically() {
      return getPageInput().getPage().isPerformWorkbenchModifierAutomatically();
   }

   @Override
   protected Tool getCurrentTool() {
      return getPageInput().getPage().getTool();
   }
}
