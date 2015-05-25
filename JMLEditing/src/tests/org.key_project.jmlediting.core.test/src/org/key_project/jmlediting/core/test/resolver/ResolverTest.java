package org.key_project.jmlediting.core.test.resolver;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.junit.Assert;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.resolver.Resolver;
import org.key_project.jmlediting.core.test.Activator;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.jdt.JDTUtil;
import org.key_project.util.test.util.TestUtilsUtil;

public class ResolverTest {

    private static IJavaProject javaProject;
    private static IFolder srcFolder;
    private static IFolder testFolder;
    private static ICompilationUnit cu;
    
    @BeforeClass
    public static void initProject() throws CoreException, InterruptedException {
       javaProject = TestUtilsUtil.createJavaProject("MainResolverTest");
       srcFolder = javaProject.getProject().getFolder("src");
       testFolder = TestUtilsUtil.createFolder(srcFolder, "mainResolverTest");
       BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/template/mainResolverTest", testFolder);
       JMLPreferencesHelper.setProjectJMLProfile(javaProject.getProject(), JMLPreferencesHelper.getDefaultJMLProfile());
       
       // Parse
       cu = (ICompilationUnit) JavaCore.create(javaProject.getProject().getFile("src/mainResolverTest/Account" + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
    }
    
    @Test
    public void resolveTest() {
        try {
            Resolver.resolve(cu);
        }
        catch (JavaModelException e) {
            e.printStackTrace();
            Assert.fail("Resolver threw a JavaModelException");
        }
    }
}
