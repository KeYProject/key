package org.key_project.jmlediting.core.test.resolver;

import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.ui.preferences.formatter.WhiteSpaceOptions.Node;
import org.junit.Assert;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.IStringNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.parser.IJMLParser;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.resolver.ResolveResult;
import org.key_project.jmlediting.core.resolver.Resolver;
import org.key_project.jmlediting.core.test.Activator;
import org.key_project.jmlediting.core.utilities.CommentLocator;
import org.key_project.jmlediting.core.utilities.CommentRange;
import org.key_project.jmlediting.core.utilities.LogUtil;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.jdt.JDTUtil;
import org.key_project.util.test.util.TestUtilsUtil;

public class ResolverTest {

    private static IJavaProject javaProject;
    private static IFolder srcFolder;
    private static IFolder testFolder;
    private static ICompilationUnit cu;
    private static List<IASTNode> iASTList = new ArrayList<IASTNode>();
    
    @BeforeClass
    public static void initProject() throws CoreException, InterruptedException {
       javaProject = TestUtilsUtil.createJavaProject("MainResolverTest");
       srcFolder = javaProject.getProject().getFolder(JDTUtil.getSourceFolderName());
       testFolder = TestUtilsUtil.createFolder(srcFolder, "mainResolverTest");
       BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/template/mainResolverTest", testFolder);
       TestUtilsUtil.waitForBuild();
       JMLPreferencesHelper.setProjectJMLProfile(javaProject.getProject(), JMLPreferencesHelper.getDefaultJMLProfile());
       
       // Parse JDT
       cu = (ICompilationUnit) JavaCore.create(javaProject.getProject().getFile("src/mainResolverTest/Account" + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
    
       // Parse JML
       IJMLParser parser = JMLPreferencesHelper.getProjectJMLProfile(javaProject.getProject()).createParser();
       CommentLocator locator = new CommentLocator(cu.getSource());
       for (final CommentRange jmlCommentRange : locator.findJMLCommentRanges()) {
           try {
               iASTList.add(parser.parse(cu.getSource(), jmlCommentRange));
           }
           catch (ParserException e) {
               LogUtil.getLogger().logError(e);
           }
       }
    }
    
    @Test
    public void resolveFieldIdentifierTest() {
        IASTNode testNode = null;
        ResolveResult result = null;
        
        
        List<IASTNode> list = Nodes.getAllNodesOfType(iASTList.get(3), NodeTypes.STRING);
        for(IASTNode node : list) {
            
            if(((IStringNode)node).getString().equals("balance")) {
                testNode = node;
                break;
            }
        }
        
        try {
            result = Resolver.resolve(cu, testNode);
        }
        catch (JavaModelException e) {
            e.printStackTrace();
            Assert.fail("Resolver threw a JavaModelException");
        }
        catch (ParserException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        
        assertTrue(result != null);
    }
}
