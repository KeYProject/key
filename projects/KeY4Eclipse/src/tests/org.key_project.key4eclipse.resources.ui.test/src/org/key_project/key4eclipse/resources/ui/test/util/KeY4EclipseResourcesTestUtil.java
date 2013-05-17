package org.key_project.key4eclipse.resources.ui.test.util;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import java.util.Arrays;
import java.util.List;

import org.eclipse.core.resources.ICommand;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.runtime.CoreException;
import org.key_project.key4eclipse.resources.builder.KeYProjectBuilder;
import org.key_project.key4eclipse.resources.nature.KeYProjectNature;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.IFilter;

public class KeY4EclipseResourcesTestUtil {

   
   
   public static void assertKeYNature(IProject project) throws CoreException {
      IProjectDescription description = project.getDescription();
      String[] natures = description.getNatureIds();
      List<String> naturesList = Arrays.asList(natures);
      assertTrue(naturesList.contains(KeYProjectNature.NATURE_ID));
      ICommand[] buildSpecs = description.getBuildSpec();
      ICommand keyBuilder = ArrayUtil.search(buildSpecs, new IFilter<ICommand>() {
         @Override
         public boolean select(ICommand element) {
            return element.getBuilderName().equals(KeYProjectBuilder.BUILDER_ID);
         }
      });
      assertNotNull(keyBuilder);
      assertEquals(KeYProjectBuilder.BUILDER_ID, keyBuilder.getBuilderName());
   }

}
