package org.key_project.sed.key.evaluation.model.tooling;

import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IWorkbenchPage;
import org.key_project.sed.key.evaluation.model.definition.Tool;
import org.key_project.sed.key.evaluation.model.input.AbstractPageInput;
import org.key_project.sed.key.evaluation.model.input.QuestionInput;

public interface IWorkbenchModifier {
   public void init(IWorkbenchPage workbenchPage, Shell shell, AbstractPageInput<?> pageInput, Tool tool);
   
   public String modifyWorkbench() throws Exception;
   
   public void cleanWorkbench() throws Exception;

   public void selectedTabChanged(QuestionInput questionInput);
}
