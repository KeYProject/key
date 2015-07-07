package org.key_project.jmlediting.profile.jmlref.test.resolver;

import static org.junit.Assert.*;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.dom.ASTMatcher;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.FieldDeclaration;
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.SingleVariableDeclaration;
import org.eclipse.jdt.core.dom.TypeDeclaration;
import org.eclipse.jdt.core.dom.VariableDeclarationFragment;
import org.junit.Assert;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.INodeTraverser;
import org.key_project.jmlediting.core.dom.IStringNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.parser.IJMLParser;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.resolver.IResolver;
import org.key_project.jmlediting.core.resolver.ResolveResult;
import org.key_project.jmlediting.core.resolver.ResolveResultType;
import org.key_project.jmlediting.core.resolver.ResolverException;
import org.key_project.jmlediting.profile.jmlref.test.Activator;
import org.key_project.jmlediting.core.utilities.CommentLocator;
import org.key_project.jmlediting.core.utilities.CommentRange;
import org.key_project.jmlediting.core.utilities.LogUtil;
import org.key_project.jmlediting.profile.jmlref.resolver.Resolver;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionNodeTypes;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.jdt.JDTUtil;
import org.key_project.util.test.testcase.JDTUtilTest;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * The ResolverTest class that is used to test the Resolver class.
 * @author Christopher Beckmann
 */
public class ResolverTest {

    private static IJavaProject javaProject;
    private static IFolder srcFolder;
    private static IFolder testFolder;
    private static ICompilationUnit cu;
    private static ICompilationUnit cu2;
    private static List<IASTNode> iASTList = new ArrayList<IASTNode>();
    private static ASTNode mainJDT;
    private static ASTNode class1JDT;
    private final static String PATH = "src/resolver/test/";
    private final static String FILE1 = "ResolverTestMain";
    private final static String FILE2 = "ResolverTestClass1";
    
    @BeforeClass
    public static void initProject() throws CoreException, InterruptedException {
       javaProject = TestUtilsUtil.createJavaProject("MainResolverTest");
       srcFolder = javaProject.getProject().getFolder(JDTUtil.getSourceFolderName());
       testFolder = TestUtilsUtil.createFolder(srcFolder, "resolver");
       testFolder = TestUtilsUtil.createFolder(testFolder, "test");
       BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data\\template\\mainResolverTest", testFolder);
       TestUtilsUtil.waitForBuild();
       JMLPreferencesHelper.setProjectJMLProfile(javaProject.getProject(), JMLPreferencesHelper.getDefaultJMLProfile());
       
       // Parse JDT
       cu = (ICompilationUnit) JavaCore.create(javaProject.getProject().getFile(PATH+FILE1+JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
       mainJDT = JDTUtil.parse(cu);
       
       // Parse JML
       final IJMLParser parser = JMLPreferencesHelper.getProjectJMLProfile(javaProject.getProject()).createParser();
       final CommentLocator locator = new CommentLocator(cu.getSource());
       for (final CommentRange jmlCommentRange : locator.findJMLCommentRanges()) {
           try {
               iASTList.add(parser.parse(cu.getSource(), jmlCommentRange));
           }
           catch (final ParserException e) {
               LogUtil.getLogger().logError(e);
           }
       }
       
       cu2 = (ICompilationUnit) JavaCore.create(javaProject.getProject().getFile(PATH+FILE2+JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
       class1JDT = JDTUtil.parse(cu2);
    }
    

    private void test(final String string, final int file, final int jdtSkip, final int jmlSkip, final ResolveResultType type) throws ResolverException {
        test(string, string, file, jdtSkip, jmlSkip, type);
    }
    private void test(final String jmlString, final String jdtString, final int file, final int jdtSkip, final int jmlSkip, final ResolveResultType type) throws ResolverException {
        final IResolver resolver = new Resolver(); // JMLPreferencesHelper.getProjectJMLProfile(javaProject.getProject())
        ResolveResult result = null;
        
        result = resolver.resolve(cu, getIASTNode(jmlString, jmlSkip));
        while(resolver.hasNext()) {
            result = resolver.next();
        }
        
        ASTNode jdt = null;
        switch(type) {
        case FIELD:
            jdt = getFieldDecleration(jdtString, file == 0 ? mainJDT : class1JDT, jdtSkip);
            break;
        case METHOD:
            jdt = getMethodDecleration(jdtString, file == 0 ? mainJDT : class1JDT, jdtSkip);
            break;
        case PARAMETER:
            jdt = getParameterDecleration(jdtString, file == 0 ? mainJDT : class1JDT, jdtSkip);
            break;
        case CLASS:
            jdt = getTypeDecleration(jdtString, file == 0 ? mainJDT : class1JDT, jdtSkip);
            break;
        case UNSPECIFIED:
            break;
        default:
            break;
        }
        
        assertNotEquals(result, null);
        
        assertTrue(result.getJDTNode().subtreeMatch(new ASTMatcher(), jdt));
        assertEquals(jdtString, result.getName());
        assertEquals(type, result.getResolveType());
        assertTrue(result.getBinding().isEqualTo(resolveBinding(jdt)));
    }
    
    @Test
    public void resolveFieldTest1() throws ResolverException {
        test("field1", 0, 0, 0, ResolveResultType.FIELD);
    }
    @Test
    public void resolveFieldTest2() throws ResolverException {
        test("field2", 0, 0, 0, ResolveResultType.FIELD);
    }
    @Test
    public void resolveFieldTest3() throws ResolverException {
        test("field3", 0, 0, 0, ResolveResultType.FIELD);
    }
    @Test
    public void resolveParameterTest1() throws ResolverException {
        test("parameter1", 0, 0, 0, ResolveResultType.PARAMETER);
    }
    @Test
    public void resolveParameterTest2() throws ResolverException {
        test("parameter2", 0, 1, 0, ResolveResultType.PARAMETER);
    }
    @Test
    public void resolveParameterTest3() throws ResolverException {
        test("parameter3", 0, 0, 0, ResolveResultType.PARAMETER);
    }
    @Test
    public void resolveParameterTest4() throws ResolverException {
        test("parameter1", 0, 1, 1, ResolveResultType.PARAMETER);
    }
    @Test
    public void resolveMethodNoParametersTest1() throws ResolverException {
        test("methodNoParameters1", 0, 0, 0, ResolveResultType.METHOD);
    }
    @Test
    public void resolveMethodNoParametersTest2() throws ResolverException {
        test("methodNoParameters2", 0, 0, 0, ResolveResultType.METHOD);
    }
    @Test
    public void resolveMethodNoParametersTest3() throws ResolverException {
        test("methodNoParameters3", 0, 0, 0, ResolveResultType.METHOD);
    }
    @Test
    public void resolveMethod1ParameterTest1() throws ResolverException {
        test("method1Parameter1", 0, 0, 0, ResolveResultType.METHOD);
    }
    @Test
    public void resolveMethod1ParameterTest2() throws ResolverException {
        test("method1Parameter2", 0, 0, 0, ResolveResultType.METHOD);
    }
    @Test
    public void resolveMethod2ParametersTest1() throws ResolverException {
        test("method2Parameters1", 0, 0, 0, ResolveResultType.METHOD);
    }
    @Test
    public void resolveMultipleFieldDeclarationTest1() throws ResolverException {
        test("fieldMultiple1", 0, 0, 0, ResolveResultType.FIELD);
    }
    @Test
    public void resolveMultipleFieldDeclarationTest2() throws ResolverException {
        test("fieldMultiple2", 0, 0, 0, ResolveResultType.FIELD);
    }
    @Test
    public void resolveArrayFieldTest1() throws ResolverException {
        test("arrayfield", "length" , 0, 0, 0, ResolveResultType.FIELD);
    }
    @Test
    public void resolveMethodSameName1ParameterTest1() throws ResolverException {
        test("methodSameName1Parameter1",  0, 1, 0, ResolveResultType.METHOD);
    }
    @Test
    public void resolveMethodSameName1ParameterTest2() throws ResolverException {
        test("methodSameName1Parameter1", 0, 0, 1, ResolveResultType.METHOD);
    }
    @Test
    public void resolveMethodComplexParameterTest1() throws ResolverException {
        test("methodComplexParameter1", 0, 0, 0, ResolveResultType.METHOD);
    }
    @Test
    public void resolveMethodComplexParameterTest2() throws ResolverException {
        test("methodComplexParameter1", 0, 0, 1, ResolveResultType.METHOD);
    }
    @Test
    public void resolveMemberAccessTest1() throws ResolverException {
        test("field3", "methodNoParameter1" , 1, 0, 3, ResolveResultType.METHOD);
    }
    @Test
    public void resolveMemberAccessTest2() throws ResolverException {
        test("field3", "method1Parameter4", 1, 0, 4, ResolveResultType.METHOD);
    }
    @Test
    public void resolveMemberAccessTest3() throws ResolverException {
        test("ResolverTestClass1", "staticMethodNoParameter10", 1, 0, 0, ResolveResultType.METHOD);
    }
    @Test
    public void resolveMemberAccessTest4() throws ResolverException {
        test("field3", "field11", 1, 0, 7, ResolveResultType.FIELD);
    }
    @Test
    public void resolveMemberAccessTest5() throws ResolverException {
        test("ResolverTestClass1", "staticField10", 1, 0, 2, ResolveResultType.FIELD);
    }
    @Test
    public void resolveMemberAccessTest6() throws ResolverException {
        test("ResolverTestClass1", "staticMethod1Parameter10", 1, 0, 1, ResolveResultType.METHOD);
    }
    @Test
    public void resolveMemberAccessTest7() throws ResolverException {
        test("field3", "field1", 1, 0, 5, ResolveResultType.FIELD);
    }
    @Test
    public void resolveMemberAccessTest8() throws ResolverException {
        test("field3", "field10", 1, 0, 6, ResolveResultType.FIELD);
    }
    @Test
    public void resolveMemberAccessTest9() throws ResolverException {
        test("field3", "getThis", 1, 0, 11, ResolveResultType.METHOD);
    }

    //TODO: write tests, that are meant to fail.

    /**
     * Helper function for the tests.
     * Gets the JDT {@link ASTNode} to verify, that the found {@link ASTNode} by the {@link Resolver} is correct.
     * @return
     */
    private ASTNode getTypeDecleration(final String name, final ASTNode context, final int skip) {
        final List<ASTNode> jdt = new LinkedList<ASTNode>();
        
        if(skip < 0) {
            return null;
        }
        
        context.accept(new ASTVisitor() {

            @Override
            public boolean visit(final TypeDeclaration node) {
                
                if(node.getName().getIdentifier().equals(name)) {
                    jdt.add(node);
                }
                
                return super.visit(node);
            }
            
        });
        if(skip >= jdt.size()) {
            return null;
        }
        
        return jdt.get(skip);
    }
    private ASTNode getFieldDecleration(final String name, final ASTNode context, final int skip) {
        final List<ASTNode> jdt = new LinkedList<ASTNode>();
        
        if(skip < 0) {
            return null;
        }
        
        context.accept(new ASTVisitor() {

            @Override
            public boolean visit(final VariableDeclarationFragment node) {
                
                if(node.getName().getIdentifier().equals(name)) {
                    jdt.add(node);
                }
                
                return super.visit(node);
            }
            
        });
        if(skip >= jdt.size()) {
            return null;
        }
        
        return jdt.get(skip);
    }
    private ASTNode getParameterDecleration(final String name, final ASTNode context, final int skip) {
        final List<ASTNode> jdt = new LinkedList<ASTNode>();
        
        if(skip < 0) {
            return null;
        }
        
        context.accept(new ASTVisitor() {

            @Override
            public boolean visit(final SingleVariableDeclaration node) {
                
                if(node.getName().getIdentifier().equals(name)) {
                    jdt.add(node);
                }
                
                return super.visit(node);
            }
            
        });
        if(skip >= jdt.size()) {
            return null;
        }
        
        return jdt.get(skip);
    }
    private ASTNode getMethodDecleration(final String name, final ASTNode context, final int skip) {
        final List<ASTNode> jdt = new LinkedList<ASTNode>();
        
        if(skip < 0) {
            return null;
        }
        
        context.accept(new ASTVisitor() {

            @Override
            public boolean visit(final MethodDeclaration node) {
                
                if(node.getName().getIdentifier().equals(name)) {
                    jdt.add(node);
                }
                
                return super.visit(node);
            }
            
        });
        if(skip >= jdt.size()) {
            return null;
        }
        
        return jdt.get(skip);
    }
    
    /**
     * Helper function for the tests.
     * Finds an IASTNode with the given identifier from the JML comments.
     * @param identifier the {@link String} that is to be searched for in the JML comments
     * @return the {@link IASTNode} that contains the {@link String}
     */
    private static IASTNode getIASTNode(final String identifier, int skip) {
        final List<IASTNode> list = new ArrayList<IASTNode>();
        
        for(final IASTNode jml : iASTList) {
             list.addAll(Nodes.getAllNodesOfType(jml, ExpressionNodeTypes.PRIMARY_EXPR));
        }
        
        
        for(final IASTNode node : list) {
            if(node.getChildren().get(0).getChildren().get(0).getType() == NodeTypes.STRING) {
                
                if(((IStringNode)node.getChildren().get(0).getChildren().get(0)).getString().equals(identifier)) {
                    if(skip-- == 0) {
                        return node;
                    }
                }
            }
        }
        return null;
    }
    
    private static IBinding resolveBinding(final ASTNode jdtNode) {
        IBinding binding = null;

        if(jdtNode instanceof TypeDeclaration) {
            binding = ((TypeDeclaration) jdtNode).resolveBinding();
        } else if(jdtNode instanceof MethodDeclaration) {
            binding = ((MethodDeclaration) jdtNode).resolveBinding();
        } else if(jdtNode instanceof SingleVariableDeclaration) {
            binding = ((SingleVariableDeclaration) jdtNode).resolveBinding();
        } else if(jdtNode instanceof VariableDeclarationFragment) {
            binding = ((VariableDeclarationFragment) jdtNode).resolveBinding();
        }
        return binding;
    }
    
    
}
