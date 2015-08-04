package org.key_project.sed.key.evaluation.model.tooling;

import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IWorkbenchPage;
import org.key_project.sed.key.evaluation.model.definition.Tool;
import org.key_project.sed.key.evaluation.model.input.AbstractPageInput;
import org.key_project.sed.key.evaluation.model.input.QuestionInput;

public abstract class AbstractWorkbenchModifier implements IWorkbenchModifier {
   private IWorkbenchPage workbenchPage;
   
   private Shell shell;
   
   private AbstractPageInput<?> pageInput;
   
   private Tool tool;

   @Override
   public void init(IWorkbenchPage workbenchPage, Shell shell, AbstractPageInput<?> pageInput, Tool tool) {
      this.workbenchPage = workbenchPage;
      this.shell = shell;
      this.pageInput = pageInput;
      this.tool = tool;
   }

   protected AbstractPageInput<?> getPageInput() {
      return pageInput;
   }

   protected Tool getTool() {
      return tool;
   }

   public Shell getShell() {
      return shell;
   }

   public IWorkbenchPage getWorkbenchPage() {
      return workbenchPage;
   }

   @Override
   public void selectedTabChanged(QuestionInput questionInput) {
   }
}
