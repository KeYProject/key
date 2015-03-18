package org.key_project.stubby.ui.wizard;

import java.lang.reflect.InvocationTargetException;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.layout.TableColumnLayout;
import org.eclipse.jface.viewers.ArrayContentProvider;
import org.eclipse.jface.viewers.ColumnWeightData;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.viewers.TableViewerColumn;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Shell;
import org.key_project.stubby.core.customization.IGeneratorCustomization;
import org.key_project.stubby.core.util.StubGeneratorUtil;
import org.key_project.stubby.core.util.StubGeneratorUtil.IgnoredType;
import org.key_project.stubby.ui.customization.IStubGenerationCustomization;
import org.key_project.stubby.ui.provider.IgnoredTypeLabelProvider;
import org.key_project.stubby.ui.util.LogUtil;
import org.key_project.stubby.ui.util.StubGenerationCustomizationUtil;
import org.key_project.stubby.ui.wizard.page.GenerateStubsWizardPage;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.eclipse.swt.dialog.ControlMessageDialog;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.thread.AbstractRunnableWithProgressAndResult;
import org.key_project.util.thread.IRunnableWithProgressAndResult;

/**
 * Stub generation {@link Wizard}.
 * @author Martin Hentschel
 */
public class GenerateStubsWizard extends Wizard {
   /**
    * The {@link IJavaProject} to generate stubs for.
    */
   private final IJavaProject javaProject;
   
   /**
    * The available {@link IStubGenerationCustomization}s.
    */
   private final List<IStubGenerationCustomization> customizations;

   /**
    * The shown {@link GenerateStubsWizardPage}.
    */
   private final GenerateStubsWizardPage generatePage;
   
   /**
    * Constructor
    * @param javaProject The {@link IJavaProject} to generate stubs for.
    */
   public GenerateStubsWizard(IJavaProject javaProject) {
      this.javaProject = javaProject;
      this.customizations = StubGenerationCustomizationUtil.createCustomizations(javaProject);
      this.generatePage = new GenerateStubsWizardPage("generatePage", javaProject, customizations);
      setWindowTitle("Generate Stubs");
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void addPages() {
      addPage(generatePage);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean performFinish() {
      try {
         final String stubFolderPath = generatePage.getStubFolderPath();
         final List<IGeneratorCustomization> generationCustomizations = new LinkedList<IGeneratorCustomization>();
         if (!CollectionUtil.isEmpty(customizations)) {
            for (IStubGenerationCustomization customization : customizations) {
               IGeneratorCustomization generatorCustomization = customization.createGeneratorCustomization();
               if (generatorCustomization != null) {
                  generationCustomizations.add(generatorCustomization);
               }
            }
         }
         final IRunnableWithProgressAndResult<List<IgnoredType>> run = new AbstractRunnableWithProgressAndResult<List<IgnoredType>>() {
            @Override
            public void run(IProgressMonitor monitor) throws InvocationTargetException, InterruptedException {
               try {
                  StubGeneratorUtil.setStubFolderPath(javaProject, stubFolderPath);
                  List<IgnoredType> ignoredTypes = StubGeneratorUtil.generateStubs(javaProject, stubFolderPath, monitor, generationCustomizations.toArray(new IGeneratorCustomization[generationCustomizations.size()]));
                  setResult(ignoredTypes);
               }
               catch (CoreException e) {
                  throw new InvocationTargetException(e, e.getMessage());
               }
            }
         };
         getContainer().run(true, false, run);
         WorkbenchUtil.selectAndReveal(javaProject.getProject().getFolder(new Path(stubFolderPath)));
         if (!CollectionUtil.isEmpty(run.getResult())) {
            ControlMessageDialog.openInformation(getShell(), 
                                                 "Information", 
                                                 "No stubs were generated for the following types:", 
                                                 new ControlMessageDialog.IControlCreator() {
               @Override
               public Control createControl(Composite parent) {
                  Composite tableComposite = new Composite(parent, SWT.NONE);
                  TableColumnLayout tableLayout = new TableColumnLayout();
                  tableComposite.setLayout(tableLayout);
                  TableViewer viewer = new TableViewer(tableComposite, SWT.BORDER | SWT.FULL_SELECTION | SWT.MULTI);
                  viewer.getTable().setHeaderVisible(true);
                  TableViewerColumn typeColumn = new TableViewerColumn(viewer, SWT.NONE);
                  typeColumn.getColumn().setText("Type");
                  typeColumn.getColumn().setResizable(true);
                  tableLayout.setColumnData(typeColumn.getColumn(), new ColumnWeightData(40));
                  TableViewerColumn reasonColumn = new TableViewerColumn(viewer, SWT.NONE);
                  reasonColumn.getColumn().setText("Reason");
                  reasonColumn.getColumn().setResizable(true);
                  tableLayout.setColumnData(reasonColumn.getColumn(), new ColumnWeightData(60));
                  SWTUtil.makeTableColumnsSortable(viewer);
                  viewer.setLabelProvider(new IgnoredTypeLabelProvider());
                  viewer.setContentProvider(ArrayContentProvider.getInstance());
                  viewer.setInput(run.getResult());
                  return tableComposite;
               }
            });
         }
         return true;
      }
      catch (OperationCanceledException e) {
         return true;
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
         LogUtil.getLogger().openErrorDialog(getShell(), e);
         return false;
      }
   }
   
   /**
    * Opens the {@link GenerateStubsWizard} in a {@link WizardDialog}.
    * @param parentShell The parent {@link Shell}.
    * @param target The {@link IJavaProject} to generate stubs for.
    * @return The dialog result.
    */
   public static int openWizard(Shell parentShell, IJavaProject javaProject) {
      WizardDialog dialog = new WizardDialog(parentShell, new GenerateStubsWizard(javaProject));
      dialog.setHelpAvailable(false);
      return dialog.open();
   }
}
