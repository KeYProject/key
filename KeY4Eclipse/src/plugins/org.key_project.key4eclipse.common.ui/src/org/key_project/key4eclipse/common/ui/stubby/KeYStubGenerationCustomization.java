package org.key_project.key4eclipse.common.ui.stubby;

import java.util.List;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.Path;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.key_project.key4eclipse.common.ui.util.LogUtil;
import org.key_project.key4eclipse.starter.core.property.KeYPathEntry;
import org.key_project.key4eclipse.starter.core.property.KeYPathEntry.KeYPathEntryKind;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties.UseBootClassPathKind;
import org.key_project.stubby.core.customization.IGeneratorCustomization;
import org.key_project.stubby.ui.customization.AbstractStubGenerationCustomization;
import org.key_project.stubby.ui.customization.IStubGenerationCustomization;
import org.key_project.util.java.ObjectUtil;

/**
 * {@link IStubGenerationCustomization} for KeY.
 * @author Martin Hentschel
 */
public class KeYStubGenerationCustomization extends AbstractStubGenerationCustomization {
   /**
    * Stub folder will be not part of class paths.
    */
   private Button doNotUseButton;
   
   /**
    * Stub folder will be part of class path.
    */
   private Button classPathButton;
   
   /**
    * Stub folder will be part of class path.
    */
   private Button bootClassPathButton;

   /**
    * Shows an explanation oft the selected options.
    */
   private Label explanationLabel;
   
   /**
    * {@inheritDoc}
    */
   @Override
   public Control createComposite(Composite parent) {
      Group keyGroup = new Group(parent, SWT.NONE);
      keyGroup.setText("KeY paths");
      keyGroup.setLayout(new GridLayout(3, false));
      doNotUseButton = new Button(keyGroup, SWT.RADIO);
      doNotUseButton.setText("&Not considered");
      doNotUseButton.setSelection(true);
      doNotUseButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            updateExplanation();
         }
      });
      classPathButton = new Button(keyGroup, SWT.RADIO);
      classPathButton.setText("&Class Path");
      classPathButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            updateExplanation();
         }
      });
      bootClassPathButton = new Button(keyGroup, SWT.RADIO);
      bootClassPathButton.setText("&Boot Class Path");
      bootClassPathButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            updateExplanation();
         }
      });
      explanationLabel = new Label(keyGroup, SWT.NONE);
      GridData explanationData = new GridData(GridData.FILL_BOTH);
      explanationData.horizontalSpan = 3;
      explanationLabel.setLayoutData(explanationData);
      updateExplanation();
      return keyGroup;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setStubFolderPath(String stubFolderPath) {
      if (isBootClassPath(stubFolderPath)) {
         doNotUseButton.setSelection(false);
         classPathButton.setSelection(false);
         bootClassPathButton.setSelection(true);
      }
      else if (isPartOfClassPath(stubFolderPath)) {
         doNotUseButton.setSelection(false);
         classPathButton.setSelection(true);
         bootClassPathButton.setSelection(false);
      }
      else {
         if (hasDefaultBootClassPath() &&
             getProject().findMember(new Path(stubFolderPath)) == null) {
            doNotUseButton.setSelection(false);
            classPathButton.setSelection(false);         
            bootClassPathButton.setSelection(true);
         }
         else {
            doNotUseButton.setSelection(true);
            classPathButton.setSelection(false);         
            bootClassPathButton.setSelection(false);
         }
      }
      updateExplanation();
   }

   /**
    * Updates the shown explanation.
    */
   protected void updateExplanation() {
      if (classPathButton.getSelection()) {
         explanationLabel.setText("Stub folder is part of KeY's class path.\n" + 
                                  "- No stubs will be generated for types contained in KeY's boot class path.\n" +
                                  "- Stubs will not contain any generics.\n" +
                                  "- Stubs are only generated for source files contained in KeY's source class path.");
      }
      else if (bootClassPathButton.getSelection()) {
         explanationLabel.setText("Stub folder is the boot class path of KeY.\n" + 
                                  "- General Java types and methods required for verification with KeY are included.\n" +
                                  "- Stubs will not contain any generics.\n" +
                                  "- Stubs are only generated for source files contained in KeY's source class path.");
      }
      else {
         explanationLabel.setText("Stub folder is not used by KeY.\n\n\n ");
      }
   }

   /**
    * Checks if the stub folder is part of the class path.
    * @param stubFolderPath The stub folder path.
    * @return {@code true} is part of class path, {@code false} is not part of class path.
    */
   protected boolean isPartOfClassPath(String stubFolderPath) {
      try {
         String fullPath = computeFullPath(stubFolderPath);
         List<KeYPathEntry> entries = KeYResourceProperties.getClassPathEntries(getProject());
         return KeYResourceProperties.searchClassPathEntry(entries, 
                                                           KeYPathEntryKind.WORKSPACE, 
                                                           fullPath) != null;
      }
      catch (CoreException e) {
         LogUtil.getLogger().logError(e);
         return false;
      }
   }
   
   /**
    * Checks if the default boot class path option is used.
    * @return {@code true} default boot class path, {@code false} other boot class path.
    */
   protected boolean hasDefaultBootClassPath() {
      try {
         return UseBootClassPathKind.KEY_DEFAULT.equals(KeYResourceProperties.getUseBootClassPathKind(getProject()));
      }
      catch (CoreException e) {
         LogUtil.getLogger().logError(e);
         return false;
      }
   }
   
   /**
    * Checks if the given stub folder is the boot class path.
    * @param stubFolderPath The stub folder path.
    * @return {@code true} is boot class path, {@code false} is not boot class path.
    */
   protected boolean isBootClassPath(String stubFolderPath) {
      return isBootClassPath(getProject(), stubFolderPath);
   }
   
   /**
    * Checks if the given stub folder is the boot class path.
    * @param project The {@link IProject} to check.
    * @param stubFolderPath The stub folder path.
    * @return {@code true} is boot class path, {@code false} is not boot class path.
    */
   public static boolean isBootClassPath(IProject project, String stubFolderPath) {
      try {
         if (UseBootClassPathKind.WORKSPACE.equals(KeYResourceProperties.getUseBootClassPathKind(project))) {
            String path = KeYResourceProperties.getBootClassPath(project);
            String fullPath = computeFullPath(project, stubFolderPath);
            return ObjectUtil.equals(fullPath, path);
         }
         else {
            return false;
         }
      }
      catch (CoreException e) {
         LogUtil.getLogger().logError(e);
         return false;
      }
   }
   
   /**
    * Computes the full path.
    * @param stubFolderPath The stub folder path.
    * @return The full path.
    */
   protected String computeFullPath(String stubFolderPath) {
      return computeFullPath(getProject(), stubFolderPath);
   }
   
   /**
    * Computes the full path.
    * @param project The parent {@link IProject}.
    * @param stubFolderPath The stub folder path.
    * @return The full path.
    */
   public static String computeFullPath(IProject project, String stubFolderPath) {
      return project.getFullPath().toString() + "/" + stubFolderPath;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IGeneratorCustomization createGeneratorCustomization() {
      return new KeYGeneratorCustomization(classPathButton.getSelection(),
                                           bootClassPathButton.getSelection());
   }
}
