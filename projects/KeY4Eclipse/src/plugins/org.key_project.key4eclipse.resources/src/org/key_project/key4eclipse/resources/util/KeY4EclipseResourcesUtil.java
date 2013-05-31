package org.key_project.key4eclipse.resources.util;

import org.eclipse.core.resources.IFile;
import org.key_project.keyide.ui.editor.KeYEditor;
import org.key_project.util.eclipse.WorkbenchUtil;

public class KeY4EclipseResourcesUtil {
   /**
    * Opens the given {@link IFile} in a {@link KeYEditor}.
    * @param file - the {@link IFile} to use
    * @throws Exception
    */
   public static void openProofFileInKeYIDE(IFile file) throws Exception {
      WorkbenchUtil.openEditor(file);
   }
}