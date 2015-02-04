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
import org.key_project.sed.core.annotation.ISEDAnnotationAppearance;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDVariable;
import org.key_project.sed.core.slicing.ISEDSlicer;
import org.key_project.sed.ui.util.LogUtil;
import org.key_project.sed.ui.wizard.page.SliceWizardPage;

/**
 * The search {@link Wizard} which performs a slicing with help of an {@link ISEDSlicer}.
 * @author Martin Hentschel
 */
public class SliceWizard extends Wizard {
   /**
    * The seed {@link ISEDDebugNode}.
    */
   private final ISEDDebugNode seedNode;

   /**
    * The seed {@link IVariable}.
    */
   private final ISEDVariable seedVariable;
   
   /**
    * The available {@link ISEDSlicer}.
    */
   private final ISEDSlicer[] slicer;
   
   /**
    * The shown {@link SliceWizardPage}.
    */
   private SliceWizardPage sliceWizardPage;

   /**
    * Constructor.
    * @param seedNode The seed {@link ISEDDebugNode}.
    * @param seedVariable The seed {@link IVariable}.
    * @param slicer The available {@link ISEDSlicer}.
    */
   public SliceWizard(ISEDDebugNode seedNode, ISEDVariable seedVariable, ISEDSlicer[] slicer) {
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
         final ISEDSlicer slicer = sliceWizardPage.getSlicer();
         final ISEDAnnotationAppearance appearance = sliceWizardPage.getAnnotationAppearance();
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
    * @param seedNode The seed {@link ISEDDebugNode}.
    * @param seedVariable The seed {@link IVariable}.
    * @param slicer The available {@link ISEDSlicer}.
    * @return The dialog result.
    */
   public static int openWizard(Shell parentShell, ISEDDebugNode seedNode, ISEDVariable seedVariable, ISEDSlicer[] slicer) {
      WizardDialog dialog = new WizardDialog(parentShell, new SliceWizard(seedNode, seedVariable, slicer));
      dialog.setHelpAvailable(false);
      return dialog.open();
   }
}
