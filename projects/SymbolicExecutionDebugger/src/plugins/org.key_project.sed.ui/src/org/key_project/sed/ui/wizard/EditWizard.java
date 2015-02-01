package org.key_project.sed.ui.wizard;

import java.lang.reflect.InvocationTargetException;

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.widgets.Shell;
import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.ui.edit.ISEDAnnotationEditor;
import org.key_project.sed.ui.util.LogUtil;
import org.key_project.sed.ui.util.SEDUIUtil;
import org.key_project.sed.ui.wizard.page.EditWizardPage;

/**
 * This {@link Wizard} is used to edit an {@link ISEDAnnotation}.
 * @author Martin Hentschel
 */
public class EditWizard extends Wizard {
   /**
    * The {@link ISEDAnnotation} to edit.
    */
   private final ISEDAnnotation annotation;
   
   /**
    * The used {@link EditWizardPage}.
    */
   private EditWizardPage editPage;
   
   /**
    * The optionally used {@link ISEDAnnotationEditor}.
    */
   private final ISEDAnnotationEditor editor;

   /**
    * Constructor.
    * @param target {@link ISEDDebugTarget} in which the {@link ISEDAnnotation} is used.
    * @param annotation The {@link ISEDAnnotation} to edit.
    */
   public EditWizard(ISEDDebugTarget target, ISEDAnnotation annotation) {
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
    * @param target {@link ISEDDebugTarget} in which the {@link ISEDAnnotation} is used.
    * @param annotation The {@link ISEDAnnotation} to edit.
    * @return The dialog result.
    */
   public static int openWizard(Shell parentShell, 
                                ISEDDebugTarget target,
                                ISEDAnnotation annotation) {
      WizardDialog dialog = new WizardDialog(parentShell, new EditWizard(target, annotation));
      return dialog.open();
   }
}
