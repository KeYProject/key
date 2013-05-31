package org.key_project.key4eclipse.resources.util;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.util.Arrays;
import java.util.Comparator;
import java.util.Iterator;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.key_project.keyide.ui.editor.KeYEditor;
import org.key_project.keyide.ui.util.KeYIDEUtil;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;



public class KeY4EclipseResourcesUtil {
   
   
   /**
    * Opens the given {@link File} in a {@link KeYEditor}.
    * @param file - the {@link File} to use
    * @throws Exception
    */
   public static void openProofFileInKeYIDE(File file) throws Exception{
      KeYEnvironment<CustomConsoleUserInterface> environment = KeYEnvironment.load(file, null, null);
      Proof proof = environment.getLoadedProof();
      KeYIDEUtil.openEditor(proof, environment);
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
   
   
   public static KeYJavaType[] sortKeYJavaTypes(Set<KeYJavaType> kjts){
      Iterator<KeYJavaType> it = kjts.iterator();
      while (it.hasNext()) {
         KeYJavaType kjt = it.next();
         if (!(kjt.getJavaType() instanceof ClassDeclaration || 
               kjt.getJavaType() instanceof InterfaceDeclaration) || 
             ((TypeDeclaration)kjt.getJavaType()).isLibraryClass()) {
            it.remove();
         }
      }
      KeYJavaType[] kjtsarr = kjts.toArray(new KeYJavaType[kjts.size()]);
      Arrays.sort(kjtsarr, new Comparator<KeYJavaType>() {
         public int compare(KeYJavaType o1, KeYJavaType o2) {
            return o1.getFullName().compareTo(o2.getFullName());
         }
      });
      return kjtsarr;
   }
}