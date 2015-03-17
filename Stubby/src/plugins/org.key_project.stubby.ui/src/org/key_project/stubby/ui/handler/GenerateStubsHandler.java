package org.key_project.stubby.ui.handler;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.resources.IProject;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.stubby.core.util.StubGeneratorUtil;
import org.key_project.stubby.ui.util.LogUtil;
import org.key_project.util.jdt.JDTUtil;

/**
 * The {@link IHandler} which is executed when the command {@code org.key_project.stubby.ui.generateStubsCommand} is triggered.
 * @author Martin Hentschel
 */
public class GenerateStubsHandler extends AbstractHandler {
   /**
    * {@inheritDoc}
    */
   @Override
   public Object execute(ExecutionEvent event) throws ExecutionException {
      // Get current selection
      ISelection selection = HandlerUtil.getCurrentSelection(event);
      if (selection instanceof IStructuredSelection) {
         try {
            for (Object element : ((IStructuredSelection) selection).toArray()) {
               IJavaProject javaProject = null;
               if (element instanceof IJavaProject) {
                  javaProject = (IJavaProject) element;
               }
               else if (element instanceof IProject) {
                  javaProject = JDTUtil.getJavaProject((IProject) element);
               }
               if (JDTUtil.isJavaProject(javaProject)) {
                  StubGeneratorUtil.generateStubs(javaProject);
               }
            }
         }
         catch (Exception e) {
            LogUtil.logError(e);
            LogUtil.openErrorDialog(e, HandlerUtil.getActiveShell(event));
         }
      }
      return null;
   }
}
