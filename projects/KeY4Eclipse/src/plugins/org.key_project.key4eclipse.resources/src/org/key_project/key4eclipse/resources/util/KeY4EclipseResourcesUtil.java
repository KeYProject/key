package org.key_project.key4eclipse.resources.util;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.key_project.keyide.ui.editor.KeYEditor;
import org.key_project.util.eclipse.WorkbenchUtil;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProofSaver;



public class KeY4EclipseResourcesUtil {
   
   
   /**
    * Opens the given {@link IFile} in a {@link KeYEditor}.
    * @param file - the {@link IFile} to use
    * @throws Exception
    */
   public static void openProofFileInKeYIDE(IFile file) throws Exception {
      WorkbenchUtil.openEditor(file);
   }
   
   
   /**
    * Saves the given {@link Proof} into the given {@link IFile}
    * @param proof - the {@link Proof} to be stored
    * @param file - the {@link IFile} to store the {@link Proof} at
    * @throws CoreException
    * @throws IOException
    */
   public static void saveProof(Proof proof, IFile file) throws CoreException, IOException{
      if(file != null){
         String filePathAndName = file.getLocation().toOSString();
         // Create proof file content
         ProofSaver saver = new ProofSaver(proof, filePathAndName, null);
         ByteArrayOutputStream out = new ByteArrayOutputStream();
         
         String errorMessage = saver.save(out);
         if (errorMessage != null) {
            throw new CoreException(LogUtil.getLogger().createErrorStatus(errorMessage));
         }
         // Save proof file content
         if (file.exists()) {
            file.setContents(new ByteArrayInputStream(out.toByteArray()), true, true, null);
         }
         else {
            file.create(new ByteArrayInputStream(out.toByteArray()), true, null);
         }
      }
   }
}