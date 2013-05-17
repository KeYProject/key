package org.key_project.key4eclipse.resources.test.util;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaCore;
import org.key_project.key4eclipse.resources.nature.KeYProjectNature;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.test.util.TestUtilsUtil;

public class KeY4EclipseResourceTestUtil {

   public static IJavaProject createKeYProject(String name) throws CoreException, InterruptedException{
      IJavaProject javaProject = TestUtilsUtil.createJavaProject(name);
      IProject project = javaProject.getProject();
      IProjectDescription description = project.getDescription();
      //Add KeYNature
      String[] natures = description.getNatureIds();
      String[] newNatures = new String[natures.length + 1];
      System.arraycopy(natures, 0, newNatures, 0, natures.length);
      newNatures[natures.length] = KeYProjectNature.NATURE_ID;
      description.setNatureIds(newNatures);
      project.setDescription(description, null);
      
      return javaProject;
   }
   
}
