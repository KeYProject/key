package org.key_project.sed.ui.wizard;

import java.lang.reflect.InvocationTargetException;

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.widgets.Shell;
import org.key_project.sed.core.annotation.ISEAnnotation;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.ui.edit.ISEAnnotationEditor;
import org.key_project.sed.ui.util.LogUtil;
import org.key_project.sed.ui.util.SEDUIUtil;
import org.key_project.sed.ui.wizard.page.EditWizardPage;

/**
 * This {@link Wizard} is used to edit an {@link ISEAnnotation}.
 * @author Martin Hentschel
 */
public class EditWizard extends Wizard {
   /**
    * The {@link ISEAnnotation} to edit.
    */
   private final ISEAnnotation annotation;
   
   /**
    * The used {@link EditWizardPage}.
    */
   private EditWizardPage editPage;
   
   /**
    * The optionally used {@link ISEAnnotationEditor}.
    */
   private final ISEAnnotationEditor editor;

   /**
    * Constructor.
    * @param target {@link ISEDebugTarget} in which the {@link ISEAnnotation} is used.
    * @param annotation The {@link ISEAnnotation} to edit.
    */
   public EditWizard(ISEDebugTarget target, ISEAnnotation annotation) {
      Assert.isNotNull(target);
      Assert.isNotNull(annotation);
      this.annotation = annotation;
      this.editor = SEDUIUtil.getAnnotationEditor(annotation.getType());
      if (editor != null) {
         this.editor.init(target, annotation);
         setNeedsProgressMonitor(editor.needsProgressMonitor());
      }
      setWindowTitle("Edit Annotation");
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void addPages() {
      editPage = new EditWizardPage("editPage", editor, annotation);
      addPage(editPage);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean performFinish() {
      if (editor != null && editor.needsProgressMonitor()) {
         try {
            getContainer().run(true, true, new IRunnableWithProgress() {
               @Override
               public void run(IProgressMonitor monitor) throws InvocationTargetException, InterruptedException {
                  try {
                     if (editor != null) {
                        editor.applyChanges(monitor);
                     }
                  }
                  catch (Exception e) {
                     throw new InvocationTargetException(e);
                  }
               }
            });
            editPage.applyChanges();
            return true;
         }
         catch (OperationCanceledException e) {
            return false;
         }
         catch (Exception e) {
            LogUtil.getLogger().logError(e);
            return false;
         }
      }
      else {
         try {
            if (editor != null) {
               editor.applyChanges(null);
            }
            editPage.applyChanges();
            return true;
         }
         catch (Exception e) {
            LogUtil.getLogger().logError(e);
            return false;
         }
      }
   }
   
   /**
    * Opens the {@link EditWizard} in a {@link WizardDialog}.
    * @param parentShell The parent {@link Shell}.
    * @param target {@link ISEDebugTarget} in which the {@link ISEAnnotation} is used.
    * @param annotation The {@link ISEAnnotation} to edit.
    * @return The dialog result.
    */
   public static int openWizard(Shell parentShell, 
                                ISEDebugTarget target,
                                ISEAnnotation annotation) {
      WizardDialog dialog = new WizardDialog(parentShell, new EditWizard(target, annotation));
      dialog.setHelpAvailable(false);
      return dialog.open();
   }
}
