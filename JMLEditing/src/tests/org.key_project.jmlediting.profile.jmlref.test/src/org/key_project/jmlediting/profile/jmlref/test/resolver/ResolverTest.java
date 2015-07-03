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
    
    private void test(final String test, final int file, final int jdtSkip, final int jmlSkip, final ResolveResultType type) {
        final IResolver resolver = new Resolver(); // JMLPreferencesHelper.getProjectJMLProfile(javaProject.getProject())
        ResolveResult result = null;
        try {
            result = resolver.resolve(cu, getIASTNode(test, jmlSkip));
            ResolveResult next = result;
            while(next != null) {
                result = next;
                next = resolver.next();
            }
        }
        catch (final ResolverException e) {
            LogUtil.getLogger().logError(e);
        }
        ASTNode jdt = null;
        switch(type) {
        case FIELD:
            jdt = getFieldDecleration(test, file == 0 ? mainJDT : class1JDT, jdtSkip);
            break;
        case METHOD:
            jdt = getMethodDecleration(test, file == 0 ? mainJDT : class1JDT, jdtSkip);
            break;
        case PARAMETER:
            jdt = getParameterDecleration(test, file == 0 ? mainJDT : class1JDT, jdtSkip);
            break;
        case CLASS:
            jdt = getTypeDecleration(test, file == 0 ? mainJDT : class1JDT, jdtSkip);
            break;
        case UNSPECIFIED:
        }
        
        assertNotEquals(result, null);
        
        assertTrue(result.getJDTNode().subtreeMatch(new ASTMatcher(), jdt));
        assertEquals(test, result.getName());
        assertEquals(type, result.getResolveType());
        assertTrue(result.getBinding().isEqualTo(resolveBinding(jdt)));
    }
    
    @Test
    public void resolveFieldTest1() {
        test("field1", 0, 0, 0, ResolveResultType.FIELD);
    }
    @Test
    public void resolveFieldTest2() {
        test("field2", 0, 0, 0, ResolveResultType.FIELD);
    }
    @Test
    public void resolveFieldTest3() {
        test("field3", 0, 0, 0, ResolveResultType.FIELD);
    }
    @Test
    public void resolveParameterTest1() {
        test("parameter1", 0, 0, 0, ResolveResultType.PARAMETER);
    }
    @Test
    public void resolveParameterTest2() {
        test("parameter2", 0, 1, 0, ResolveResultType.PARAMETER);
    }
    @Test
    public void resolveParameterTest3() {
        test("parameter3", 0, 0, 0, ResolveResultType.PARAMETER);
    }
    @Test
    public void resolveParameterTest4() {
        test("parameter1", 0, 1, 1, ResolveResultType.PARAMETER);
    }
    @Test
    public void resolveMethodNoParametersTest1() {
        test("methodNoParameters1", 0, 0, 0, ResolveResultType.METHOD);
    }
    @Test
    public void resolveMethodNoParametersTest2() {
        test("methodNoParameters2", 0, 0, 0, ResolveResultType.METHOD);
    }
    @Test
    public void resolveMethodNoParametersTest3() {
        test("methodNoParameters3", 0, 0, 0, ResolveResultType.METHOD);
    }
    @Test
    public void resolveMethod1ParameterTest1() {
        test("method1Parameter1", 0, 0, 0, ResolveResultType.METHOD);
    }
    @Test
    public void resolveMethod1ParameterTest2() {
        test("method1Parameter2", 0, 0, 0, ResolveResultType.METHOD);
    }
    @Test
    public void resolveMethod2ParametersTest1() {
        test("method2Parameters1", 0, 0, 0, ResolveResultType.METHOD);
    }
    @Test
    public void resolveMethodSameName1ParameterTest1() {
        test("methodSameName1Parameter1", 0, 1, 0, ResolveResultType.METHOD);
    }
    @Test
    public void resolveMultipleFieldDeclarationTest1() {
        test("fieldMultiple1", 0, 0, 0, ResolveResultType.FIELD);
    }
    @Test
    public void resolveMultipleFieldDeclarationTest2() {
        test("fieldMultiple2", 0, 0, 0, ResolveResultType.FIELD);
    }
    @Test
    public void resolveArrayFieldTest1() {
        test("arrayfield", 0, 0, 0, ResolveResultType.FIELD);
    }
    @Test
    public void resolveMethodSameName1ParameterTest2() {
        test("methodSameName1Parameter1", 0, 0, 1, ResolveResultType.METHOD);
    }
    @Test
    public void resolveMethodComplexParameterTest1() {
        test("methodComplexParameter1", 0, 0, 0, ResolveResultType.METHOD);
    }
    @Test
    public void resolveMethodComplexParameterTest2() {
        test("methodComplexParameter1", 0, 1, 1, ResolveResultType.METHOD);
    }
    @Test
    public void resolveMemberAccessTest1() {
        test("methodNoParameter1", 1, 0, 1, ResolveResultType.METHOD);
    }
    @Test
    public void resolveMemberAccessTest2() {
        test("method1Parameter4", 1, 0, 0, ResolveResultType.METHOD);
    }
    @Test
    public void resolveMemberAccessTest3() {
        test("staticMethodNoParameter10", 1, 0, 0, ResolveResultType.METHOD);
    }
    @Test
    public void resolveMemberAccessTest4() {
        test("field11", 1, 0, 0, ResolveResultType.FIELD);
    }
    @Test
    public void resolveMemberAccessTest5() {
        test("staticField10", 1, 0, 0, ResolveResultType.FIELD);
    }
    @Test
    public void resolveMemberAccessTest6() {
        test("staticMethod1Parameter10", 1, 0, 0, ResolveResultType.METHOD);
    }
    @Test
    public void resolveMemberAccessTest7() {
        test("field1", 1, 0, 5, ResolveResultType.FIELD);
    }
    @Test
    public void resolveMemberAccessTest8() {
        test("field10", 1, 0, 0, ResolveResultType.FIELD);
    }
    @Test
    public void resolveMemberAccessTest9() {
        test("ResolverTestClass1", 1, 0, 0, ResolveResultType.CLASS);
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
