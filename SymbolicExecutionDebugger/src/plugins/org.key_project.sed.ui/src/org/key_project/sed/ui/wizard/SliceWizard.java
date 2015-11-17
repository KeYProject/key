package org.key_project.sed.ui.wizard;

import java.lang.reflect.InvocationTargetException;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.model.IVariable;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.widgets.Shell;
import org.key_project.sed.core.annotation.ISEAnnotationAppearance;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEVariable;
import org.key_project.sed.core.slicing.ISESlicer;
import org.key_project.sed.ui.util.LogUtil;
import org.key_project.sed.ui.wizard.page.SliceWizardPage;

/**
 * The search {@link Wizard} which performs a slicing with help of an {@link ISESlicer}.
 * @author Martin Hentschel
 */
public class SliceWizard extends Wizard {
   /**
    * The seed {@link ISENode}.
    */
   private final ISENode seedNode;

   /**
    * The seed {@link IVariable}.
    */
   private final ISEVariable seedVariable;
   
   /**
    * The available {@link ISESlicer}.
    */
   private final ISESlicer[] slicer;
   
   /**
    * The shown {@link SliceWizardPage}.
    */
   private SliceWizardPage sliceWizardPage;

   /**
    * Constructor.
    * @param seedNode The seed {@link ISENode}.
    * @param seedVariable The seed {@link IVariable}.
    * @param slicer The available {@link ISESlicer}.
    */
   public SliceWizard(ISENode seedNode, ISEVariable seedVariable, ISESlicer[] slicer) {
      this.seedNode = seedNode;
      this.seedVariable = seedVariable;
      this.slicer = slicer;
      setWindowTitle("Slice Symbolic Execution Tree");
      setNeedsProgressMonitor(true);
      setHelpAvailable(false);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void addPages() {
      sliceWizardPage = new SliceWizardPage("sliceWizardPage", slicer);
      addPage(sliceWizardPage);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean performFinish() {
      try {
         final ISESlicer slicer = sliceWizardPage.getSlicer();
         final ISEAnnotationAppearance appearance = sliceWizardPage.getAnnotationAppearance();
         getContainer().run(true, true, new IRunnableWithProgress() {
            @Override
            public void run(IProgressMonitor monitor) throws InvocationTargetException, InterruptedException {
               try {
                  monitor.beginTask("Slicing Symbolic Execution Tree", IProgressMonitor.UNKNOWN);
                  slicer.slice(seedNode, seedVariable, appearance, monitor);
               }
               catch (DebugException e) {
                  throw new InvocationTargetException(e);
               }
               finally {
                  monitor.done();
               }
            }
         });
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
   
   /**
    * Opens the {@link SliceWizard} in a {@link WizardDialog}.
    * @param parentShell The parent {@link Shell}.
    * @param seedNode The seed {@link ISENode}.
    * @param seedVariable The seed {@link IVariable}.
    * @param slicer The available {@link ISESlicer}.
    * @return The dialog result.
    */
   public static int openWizard(Shell parentShell, ISENode seedNode, ISEVariable seedVariable, ISESlicer[] slicer) {
      WizardDialog dialog = new WizardDialog(parentShell, new SliceWizard(seedNode, seedVariable, slicer));
      dialog.setHelpAvailable(false);
      return dialog.open();
   }
}
