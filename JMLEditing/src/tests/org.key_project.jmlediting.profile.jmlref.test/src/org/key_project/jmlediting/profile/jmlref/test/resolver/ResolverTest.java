package org.key_project.jmlediting.profile.jmlref.test.resolver;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.dom.ASTMatcher;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.SingleVariableDeclaration;
import org.eclipse.jdt.core.dom.TypeDeclaration;
import org.eclipse.jdt.core.dom.VariableDeclarationFragment;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.IKeywordNode;
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
import org.key_project.jmlediting.core.utilities.CommentLocator;
import org.key_project.jmlediting.core.utilities.CommentRange;
import org.key_project.jmlediting.core.utilities.LogUtil;
import org.key_project.jmlediting.profile.jmlref.resolver.Resolver;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionNodeTypes;
import org.key_project.jmlediting.profile.jmlref.test.Activator;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.jdt.JDTUtil;
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
    private static List<IASTNode> iASTListParam = new ArrayList<IASTNode>();
    private static List<IASTNode> iASTListParam2 = new ArrayList<IASTNode>();
    private static ASTNode mainJDT;
    private static ASTNode superJDT;
    private static ASTNode class1JDT;
    private static ASTNode class2JDT;
    private static ICompilationUnit cu3;
    private static ICompilationUnit cuSuper;
    private static ICompilationUnit cuParam;
    private static ASTNode paramJDT;
    private static ICompilationUnit cuBound1;
    private static ASTNode bound1JDT;
    private static ICompilationUnit cuBound2;
    private static ASTNode bound2JDT;
    private static ICompilationUnit cuBound3;
    private static ASTNode bound3JDT;
   private static ICompilationUnit cuParam2;
   private static ASTNode param2JDT;
    private final static String PATH = "src/resolver/test/";
    private final static String FILE1 = "ResolverTestMain";
    private final static String FILE2 = "ResolverTestClass1";
    private final static String PATHFILE3 = "src/resolver/test/otherPackage/ResolverTestClass2";
    private final static String FILE4 = "ResolverTestSuper";
    private final static String PATH2 = "src/resolver/test/parameterizedTypeTest/";
    private final static String FILE5 = "Main";
    private final static String FILE6 = "Bound1";
    private final static String FILE7 = "IBound2";
    private final static String FILE8 = "IBound3";
    private final static String FILE9 = "Main2";
    
    
    
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
       cu2 = (ICompilationUnit) JavaCore.create(javaProject.getProject().getFile(PATH+FILE2+JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
       class1JDT = JDTUtil.parse(cu2);
       cu3 = (ICompilationUnit) JavaCore.create(javaProject.getProject().getFile(PATHFILE3+JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
       class2JDT = JDTUtil.parse(cu3);
       cuSuper = (ICompilationUnit) JavaCore.create(javaProject.getProject().getFile(PATH+FILE4+JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
       superJDT = JDTUtil.parse(cuSuper);
       cuParam = (ICompilationUnit) JavaCore.create(javaProject.getProject().getFile(PATH2+FILE5+JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
       paramJDT = JDTUtil.parse(cuParam);
       cuBound1 = (ICompilationUnit) JavaCore.create(javaProject.getProject().getFile(PATH2+FILE6+JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
       bound1JDT = JDTUtil.parse(cuBound1);
       cuBound2 = (ICompilationUnit) JavaCore.create(javaProject.getProject().getFile(PATH2+FILE7+JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
       bound2JDT = JDTUtil.parse(cuBound2);
       cuBound3 = (ICompilationUnit) JavaCore.create(javaProject.getProject().getFile(PATH2+FILE8+JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
       bound3JDT = JDTUtil.parse(cuBound3);
       cuParam2 = (ICompilationUnit) JavaCore.create(javaProject.getProject().getFile(PATH2+FILE9+JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
       param2JDT = JDTUtil.parse(cuParam2);
       
       // Parse JML
       final IJMLParser parser = JMLPreferencesHelper.getProjectJMLProfile(javaProject.getProject()).createParser();
       for (final CommentRange jmlCommentRange : CommentLocator.listJMLCommentRanges(cu.getSource())) {
           try {
               iASTList.add(parser.parse(cu.getSource(), jmlCommentRange));
           }
           catch (final ParserException e) {
               LogUtil.getLogger().logError(e);
           }
       }
       final IJMLParser parser2 = JMLPreferencesHelper.getProjectJMLProfile(javaProject.getProject()).createParser();
       for (final CommentRange jmlCommentRange : CommentLocator.listJMLCommentRanges(cuParam.getSource())) {
           try {
               iASTListParam.add(parser2.parse(cuParam.getSource(), jmlCommentRange));
           }
           catch (final ParserException e) {
               LogUtil.getLogger().logError(e);
           }
       }
       final IJMLParser parser3 = JMLPreferencesHelper.getProjectJMLProfile(javaProject.getProject()).createParser();
       for (final CommentRange jmlCommentRange : CommentLocator.listJMLCommentRanges(cuParam2.getSource())) {
           try {
               iASTListParam2 .add(parser3.parse(cuParam2.getSource(), jmlCommentRange));
           }
           catch (final ParserException e) {
               LogUtil.getLogger().logError(e);
           }
       }
       
    }
    

    private void test(final String string, final int file, final int jdtSkip, final int jmlSkip, final ResolveResultType type) throws ResolverException {
        test(0, string, string, file, jdtSkip, jmlSkip, type, null);
    }
    
    private void test(final int testFile, final String jmlString, final String jdtString, final int file, final int jdtSkip, final int jmlSkip, final ResolveResultType type, final IASTNode nodeToResolve) throws ResolverException {
       test(testFile, jmlString, jdtString, file, jdtSkip, jmlSkip, type, nodeToResolve, false);
    }
    
    private void test(final int testFile, final String jmlString, final String jdtString, final int file, final int jdtSkip, final int jmlSkip, final ResolveResultType type, final IASTNode nodeToResolve, final boolean resultIsBinary) throws ResolverException {
        final IResolver resolver = new Resolver(); // JMLPreferencesHelper.getProjectJMLProfile(javaProject.getProject())
        ResolveResult result = null;
        
        ICompilationUnit compUnit = null;
        switch(testFile) {
        case 0:  
           compUnit = cu;
           break;
        case 1:
           compUnit = cuParam;
           break;
        case 2:
           compUnit = cuParam2;
           break;
        default:
           return;
        }
        
        if (nodeToResolve == null) {
            result = resolver.resolve(compUnit, getIASTNode(jmlString, jmlSkip, testFile));
        }
        else {
            result = resolver.resolve(compUnit, nodeToResolve);
        }
        while(resolver.hasNext()) {
            result = resolver.next();
        }
        
        ASTNode jdt = null;
        
        ASTNode resultFile = null;
        switch(file){
        case 0:
            resultFile = mainJDT;
            break;
        case 1:
            resultFile = class1JDT;
            break;
        case 2:
            resultFile = class2JDT;
            break;
        case 3:
           resultFile = superJDT;
           break;
        case 4: 
           resultFile = paramJDT;
           break;
        case 5:
           resultFile = bound1JDT;
           break;
        case 6:
           resultFile = bound2JDT;
           break;
        case 7:
           resultFile = bound3JDT;
           break;
        case 8:
           resultFile = param2JDT;
           break;
        default:
            return;
        }
        
        switch(type) {
        case FIELD:
            jdt = getFieldDecleration(jdtString, resultFile, jdtSkip);
            break;
        case METHOD:
            jdt = getMethodDecleration(jdtString, resultFile, jdtSkip);
            break;
        case PARAMETER:
            jdt = getParameterDecleration(jdtString, resultFile, jdtSkip);
            break;
        case CLASS:
            jdt = getTypeDecleration(jdtString, resultFile, jdtSkip);
            break;
        case UNSPECIFIED:
            break;
        default:
            break;
        }
        
        assertNotEquals(result, null);
        
        if(!resultIsBinary) {
         assertTrue(result.getJDTNode().subtreeMatch(new ASTMatcher(), jdt));
        }
        assertEquals(jdtString, result.getName());
        assertEquals(type, result.getResolveType());
        if(!resultIsBinary) {
         assertTrue(result.getBinding().isEqualTo(resolveBinding(jdt)));
        }
    }
    private void importTest(final String jmlString, final String jdtString, final int jmlSkip, final ResolveResultType type) throws ResolverException {
        final IResolver resolver = new Resolver(); // JMLPreferencesHelper.getProjectJMLProfile(javaProject.getProject())
        ResolveResult result = null;
        
        result = resolver.resolve(cu, getIASTNode(jmlString, jmlSkip));
        while(resolver.hasNext()) {
            result = resolver.next();
        }        
        assertNotEquals(result, null);
        
        assertEquals(jdtString, result.getName());
        assertEquals(type, result.getResolveType());
    }

    /** This method just calls the {@link Resolver} with the given string. This method is supposed to be called from tests, that want to test for an exception, since this method will not compare results.
     * @param jmlString the name of the method, field or class you want to resolve. It will be searched in the test file.
     * @param jmlSkip the amount of times the found string will be skipped until it is considered to be resolved. 
     * @throws ResolverException is thrown if the resolver throws one
     */
    private void exceptionTest(final String jmlString, final int jmlSkip) throws ResolverException {
        final IResolver resolver = new Resolver();
        
        resolver.resolve(cu, getIASTNode(jmlString, jmlSkip));
        while(resolver.hasNext()) {
            resolver.next();
        }        
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
        test(0, "field3", "methodNoParameter1" , 1, 0, 3, ResolveResultType.METHOD, null);
    }
    @Test
    public void resolveMemberAccessTest2() throws ResolverException {
        test(0, "field3", "method1Parameter4", 1, 0, 4, ResolveResultType.METHOD, null);
    }
    @Test
    public void resolveMemberAccessTest3() throws ResolverException {
        test(0, "ResolverTestClass1", "staticMethodNoParameter10", 1, 0, 0, ResolveResultType.METHOD, null);
    }
    @Test
    public void resolveMemberAccessTest4() throws ResolverException {
        test(0, "field3", "field11", 1, 0, 7, ResolveResultType.FIELD, null);
    }
    @Test
    public void resolveMemberAccessTest5() throws ResolverException {
        test(0, "ResolverTestClass1", "staticField10", 1, 0, 2, ResolveResultType.FIELD, null);
    }
    @Test
    public void resolveMemberAccessTest6() throws ResolverException {
        test(0, "ResolverTestClass1", "staticMethod1Parameter10", 1, 0, 1, ResolveResultType.METHOD, null);
    }
    @Test
    public void resolveMemberAccessTest7() throws ResolverException {
        test(0, "field3", "field1", 1, 0, 5, ResolveResultType.FIELD, null);
    }
    @Test
    public void resolveMemberAccessTest8() throws ResolverException {
        test(0, "field3", "field10", 1, 0, 6, ResolveResultType.FIELD, null);
    }
    @Test
    public void resolveMemberAccessTest9() throws ResolverException {
        test(0, "field3", "getThis", 1, 0, 11, ResolveResultType.METHOD, null);
    }
    @Test
    public void resolveCastExpression() throws ResolverException {
        test(0, "castMethodAndThis", "field1", 1, 0, 0, ResolveResultType.FIELD, getIASTNodeCast("ResolverTestClass1"));
    }
    @Test
    public void resolvePackageImportType1() throws ResolverException {
        importTest("integer", "add", 1, ResolveResultType.METHOD);
    }
    @Test
    public void resolvePackageImportParameterizedType1() throws ResolverException {
        importTest("field4", "containsKey", 1, ResolveResultType.METHOD);
    }
    @Test
    public void resolvePackageImportParameterizedType2() throws ResolverException {
        importTest("field4", "put", 2, ResolveResultType.METHOD);
    }
    @Test
    public void resolveParameterizedType3() throws ResolverException {
       importTest("arraylist", "equals", 0,ResolveResultType.METHOD);
    }
    @Test
    public void resolvePackageImportOnDemand1() throws ResolverException {
        importTest("fr", "read", 0, ResolveResultType.METHOD);
    }
    @Test
    public void resolveStaticImportField() throws ResolverException {
        test("staticField", 2, 0, 0, ResolveResultType.FIELD);
    }
    @Test
    public void resolveStaticImportMethod() throws ResolverException {
        test("staticMethod", 2, 0, 0, ResolveResultType.METHOD);
    }
    @Test
    public void resolveMultipleApplicableMethods() throws ResolverException {
        test("sameNameApplicable", 0, 0, 0, ResolveResultType.METHOD);
    }
    @Test(expected=ResolverException.class)
    public void resolveAmbiguousMethod() throws ResolverException {
        exceptionTest("ambiguousMethod", 0);
    }
    @Test
    public void resolveWrongParameterTest() throws ResolverException {
       final IResolver resolver = new Resolver();
       ResolveResult result = null;
       
       result = resolver.resolve(cu, null);
       assertEquals(null, result);
       
       result = resolver.resolve(null, getIASTNode("field1", 0));
       assertEquals(null, result);
    }
    @Test
    public void resolveTooManyNextCalls() throws ResolverException {
       final IResolver resolver = new Resolver();
       ResolveResult result = null;
       
       result = resolver.resolve(cu, getIASTNode("field1", 0));
       
       while(resolver.hasNext()) {
           result = resolver.next();
       }
       // call it once more.
       result = resolver.next();
       assertEquals(null, result);
    }
    @Test(expected=ResolverException.class)
    public void resolveWrongIASTNode() throws ResolverException {
       final IResolver resolver = new Resolver();
       
       final IASTNode mark = getIASTNode("parameter1", 0);
       final IASTNode newNode = iASTList.get(10).traverse(new INodeTraverser<IASTNode>() {

         @Override
         public IASTNode traverse(final IASTNode node, final IASTNode existing) {
            if(node.containsOffset(mark.getStartOffset()) && node.getType() == ExpressionNodeTypes.EQUALITY) {
               return node;
            }
            return existing;
         }
          
       }, mark);
       
       resolver.resolve(cu, newNode);
    }
    @Test
    public void resolveArrayAccess() throws ResolverException {
       final IResolver resolver = new Resolver();
       ResolveResult result = null;
       
       result = resolver.resolve(cu, getIASTNode("arrayField2", 0));
       
       while(resolver.hasNext()) {
           result = resolver.next();
       }
       
       assertNotEquals(null, result);
       
       final ASTNode jdt = getFieldDecleration("arrayField2", mainJDT, 0);
       
       assertTrue(result.getJDTNode().subtreeMatch(new ASTMatcher(), jdt));
       assertEquals("arrayField2", result.getName());
       assertEquals(ResolveResultType.ARRAY_ACCESS, result.getResolveType());
       assertTrue(result.getBinding().isEqualTo(((IVariableBinding)resolveBinding(jdt)).getType().getComponentType()));
    }
    @Test(expected=ResolverException.class)
    public void resolveAccessToPrimitiveType() throws ResolverException {
       exceptionTest("primitiveField", 0);
    }
    @Test(expected=ResolverException.class)
    public void resolveArrayAccessToNonArrayType() throws ResolverException {
       exceptionTest("primitiveField", 1);
    }
    @Test
    public void resolveArrayLength() throws ResolverException {
       final IResolver resolver = new Resolver();
       ResolveResult result = null;
       
       result = resolver.resolve(cu, getIASTNode("arrayfield", 0));
       
       while(resolver.hasNext()) {
           result = resolver.next();
       }
       
       assertNotEquals(null, result);
       
       assertEquals(null, result.getJDTNode());
       assertEquals("length", result.getName());
       assertEquals(ResolveResultType.ARRAY_LENGTH, result.getResolveType());
       assertTrue(result.getBinding().isEqualTo(mainJDT.getAST().resolveWellKnownType("int")));
    }
    @Test
    public void resolveClassImportBinaryAndCast() throws ResolverException {
       final IResolver resolver = new Resolver();
       ResolveResult result = null;
       
       result = resolver.resolve(cu, getIASTNodeCast("BigInteger"));
       
       while(resolver.hasNext()) {
           result = resolver.next();
       }
       
       assertNotEquals(null, result);
       
       assertNotEquals(null, result.getJDTNode());
       assertEquals("add", result.getName());
       assertEquals(ResolveResultType.METHOD, result.getResolveType());
    }
    @Test
    public void resolveThisKeyword() throws ResolverException {
       test(0, "this", "field2", 0, 0, 0, ResolveResultType.FIELD, null);
    }
    @Test
    public void resolveSuperKeyword() throws ResolverException {
       test(0, "super", "superField", 3, 0, 0, ResolveResultType.FIELD, null);
    }
    @Test
    public void resolveMethodInSuperClass() throws ResolverException {
       test("superMethod", 3, 0, 0, ResolveResultType.METHOD);
    }
    @Test
    public void resolveFieldInSuperClass() throws ResolverException {
       test("superField", 3, 0, 0, ResolveResultType.FIELD);
    }
    @Test
    public void resolveFullyReferencedClassCast() throws ResolverException {
       final IResolver resolver = new Resolver();
       ResolveResult result = null;
       
       result = resolver.resolve(cu, getIASTNodeCast("java"));
       
       while(resolver.hasNext()) {
           result = resolver.next();
       }
       
       assertNotEquals(null, result);
       
       assertNotEquals(null, result.getJDTNode());
       assertEquals("add", result.getName());
       assertEquals(ResolveResultType.METHOD, result.getResolveType());
    }
    @Test
    public void resolveOnDemandImport() throws ResolverException {
       final IResolver resolver = new Resolver();
       ResolveResult result = null;

       result = resolver.resolve(cu, getIASTNodeCast("FileReader"));
       
       while(resolver.hasNext()) {
           result = resolver.next();
       }
       
       assertNotEquals(null, result);
       
       assertNotEquals(null, result.getJDTNode());
       assertEquals("read", result.getName());
       assertEquals(ResolveResultType.METHOD, result.getResolveType());
    }
    @Test
    public void resolveMethodBoxingUnboxingBoolean() throws ResolverException {
       test("booleanMethod", 0, 0, 0, ResolveResultType.METHOD);
       //@ invariant booleanMethod(booleanField, _booleanField);
    }
    @Test
    public void resolveMethodBoxingUnboxingByte() throws ResolverException {
       test("byteMethod", 0, 0, 0, ResolveResultType.METHOD);
       //@ invariant byteMethod(byteField, _byteField);
       //@ invariant shortMethod(shortField, _shortField);
       //@ invariant charMethod(charField, _charField);
       //@ invariant longMethod(longField, _longField);
       //@ invariant floatMethod(floatField, _floatField);
       //@ invariant doubleMethod(doubleField, _doubleField);
    }
    @Test
    public void resolveMethodBoxingUnboxingShort() throws ResolverException {
       test("shortMethod", 0, 0, 0, ResolveResultType.METHOD);
       //@ invariant shortMethod(shortField, _shortField);
    }
    @Test
    public void resolveMethodBoxingUnboxingChar() throws ResolverException {
       test("charMethod", 0, 0, 0, ResolveResultType.METHOD);
       //@ invariant charMethod(charField, _charField);
    }
    @Test
    public void resolveMethodBoxingUnboxingLong() throws ResolverException {
       test("longMethod", 0, 0, 0, ResolveResultType.METHOD);
       //@ invariant longMethod(longField, _longField);
    }
    @Test
    public void resolveMethodBoxingUnboxingFloat() throws ResolverException {
       test("floatMethod", 0, 0, 0, ResolveResultType.METHOD);
       //@ invariant floatMethod(floatField, _floatField);
    }
    @Test
    public void resolveMethodBoxingUnboxingDouble() throws ResolverException {
       test("doubleMethod", 0, 0, 0, ResolveResultType.METHOD);
       //@ invariant doubleMethod(doubleField, _doubleField);
    }
    @Test
    public void resolveMethodBoxingUnboxingInt() throws ResolverException {
       test("intMethod", 0, 0, 0, ResolveResultType.METHOD);
       //@ invariant intMethod(intField, _intField);
    }
    //  byte -> short | int | long | float | double
    //@ invariant shortMethod(byteField, _byteField);
    //@ invariant intMethod(byteField, _byteField);
    //@ invariant longMethod(byteField, _byteField);
    //@ invariant floatMethod(byteField, _byteField);
    //@ invariant doubleMethod(byteField, _byteField);
    @Test
    public void resolveMethodWideningPrimitiveConversionByte1() throws ResolverException {
       test("shortMethod", 0, 0, 1, ResolveResultType.METHOD);
    }
    @Test
    public void resolveMethodWideningPrimitiveConversionByte2() throws ResolverException {
       test("intMethod", 0, 0, 1, ResolveResultType.METHOD);
    }
    @Test
    public void resolveMethodWideningPrimitiveConversionByte3() throws ResolverException {
       test("longMethod", 0, 0, 1, ResolveResultType.METHOD);
    }
    @Test
    public void resolveMethodWideningPrimitiveConversionByte4() throws ResolverException {
       test("floatMethod", 0, 0, 1, ResolveResultType.METHOD);
    }
    @Test
    public void resolveMethodWideningPrimitiveConversionByte5() throws ResolverException {
       test("doubleMethod", 0, 0, 1, ResolveResultType.METHOD);
    }
      //      short -> int | long | float | double 
      //@ invariant intMethod(shortField, _shortField);
      //@ invariant longMethod(shortField, _shortField);
      //@ invariant floatMethod(shortField, _shortField);
      //@ invariant doubleMethod(shortField, _shortField);
    @Test
    public void resolveMethodWideningPrimitiveConversionShort1() throws ResolverException {
       test("intMethod", 0, 0, 2, ResolveResultType.METHOD);
    }
    @Test
    public void resolveMethodWideningPrimitiveConversionShort2() throws ResolverException {
       test("longMethod", 0, 0, 2, ResolveResultType.METHOD);
    }
    @Test
    public void resolveMethodWideningPrimitiveConversionShort3() throws ResolverException {
       test("floatMethod", 0, 0, 2, ResolveResultType.METHOD);
    }
    @Test
    public void resolveMethodWideningPrimitiveConversionShort4() throws ResolverException {
       test("doubleMethod", 0, 0, 2, ResolveResultType.METHOD);
    }
      //      char -> int | long | float | double
      //@ invariant intMethod(charField, _charField);
      //@ invariant longMethod(charField, _charField);
      //@ invariant floatMethod(charField, _charField);
      //@ invariant doubleMethod(charField, _charField);
    @Test
    public void resolveMethodWideningPrimitiveConversionChar1() throws ResolverException {
       test("intMethod", 0, 0, 3, ResolveResultType.METHOD);
    }
    @Test
    public void resolveMethodWideningPrimitiveConversionChar2() throws ResolverException {
       test("longMethod", 0, 0, 3, ResolveResultType.METHOD);
    }
    @Test
    public void resolveMethodWideningPrimitiveConversionChar3() throws ResolverException {
       test("floatMethod", 0, 0, 3, ResolveResultType.METHOD);
    }
    @Test
    public void resolveMethodWideningPrimitiveConversionChar4() throws ResolverException {
       test("doubleMethod", 0, 0, 3, ResolveResultType.METHOD);
    }
      //      int -> long | float | double
      //@ invariant longMethod(intField, _intField);
      //@ invariant floatMethod(intField, _intField);
      //@ invariant doubleMethod(intField, _intField);
    @Test
    public void resolveMethodWideningPrimitiveConversionInt1() throws ResolverException {
       test("longMethod", 0, 0, 4, ResolveResultType.METHOD);
    }
    @Test
    public void resolveMethodWideningPrimitiveConversionInt2() throws ResolverException {
       test("floatMethod", 0, 0, 4, ResolveResultType.METHOD);
    }
    @Test
    public void resolveMethodWideningPrimitiveConversionInt3() throws ResolverException {
       test("doubleMethod", 0, 0, 4, ResolveResultType.METHOD);
    }
      //      long -> float | double
      //@ invariant floatMethod(longField, _longField);
      //@ invariant doubleMethod(longField, _longField);
    @Test
    public void resolveMethodWideningPrimitiveConversionLong1() throws ResolverException {
       test("floatMethod", 0, 0, 5, ResolveResultType.METHOD);
    }
    @Test
    public void resolveMethodWideningPrimitiveConversionLong2() throws ResolverException {
       test("doubleMethod", 0, 0, 5, ResolveResultType.METHOD);
    }
      //      float -> double
      //@ invariant doubleMethod(floatField, _floatField);
    @Test
    public void resolveMethodWideningPrimitiveConversionFloat1() throws ResolverException {
       test("doubleMethod", 0, 0, 6, ResolveResultType.METHOD);
    }
    //@ invariant serializableMethod(booleanField);
    @Test
    public void resolveMethodWideningReferenceConversion1() throws ResolverException {
       test("serializableMethod", 0, 0, 0, ResolveResultType.METHOD);
    }
    //@ invariant serializableMethod(byteField);
    @Test
    public void resolveMethodWideningReferenceConversion2() throws ResolverException {
       test("serializableMethod", 0, 0, 1, ResolveResultType.METHOD);
    }
    //@ invariant serializableMethod(shortField);
    @Test
    public void resolveMethodWideningReferenceConversion3() throws ResolverException {
       test("serializableMethod", 0, 0, 2, ResolveResultType.METHOD);
    }
    //@ invariant serializableMethod(charField);
    @Test
    public void resolveMethodWideningReferenceConversion4() throws ResolverException {
       test("serializableMethod", 0, 0, 3, ResolveResultType.METHOD);
    }
    //@ invariant serializableMethod(intField);
    @Test
    public void resolveMethodWideningReferenceConversion5() throws ResolverException {
       test("serializableMethod", 0, 0, 4, ResolveResultType.METHOD);
    }
    //@ invariant serializableMethod(longField);
    @Test
    public void resolveMethodWideningReferenceConversion6() throws ResolverException {
       test("serializableMethod", 0, 0, 5, ResolveResultType.METHOD);
    }
    //@ invariant serializableMethod(floatField);
    @Test
    public void resolveMethodWideningReferenceConversion7() throws ResolverException {
       test("serializableMethod", 0, 0, 6, ResolveResultType.METHOD);
    }
    //@ invariant serializableMethod(doubleField);
    @Test
    public void resolveMethodWideningReferenceConversion8() throws ResolverException {
       test("serializableMethod", 0, 0, 7, ResolveResultType.METHOD);
    }
    @Test 
    public void resolveParameterizedTypeTest1() throws ResolverException {
       test(1, "field", "methodFromBound1", 5, 0, 0, ResolveResultType.METHOD, null);
    }
    @Test 
    public void resolveParameterizedTypeTest2() throws ResolverException {
       test(1, "field", "methodFromIBound2", 6, 0, 1, ResolveResultType.METHOD, null);
    }
    @Test 
    public void resolveParameterizedTypeTest3() throws ResolverException {
       test(1, "field", "methodFromIBound3", 7, 0, 2, ResolveResultType.METHOD, null);
    }
    @Test 
    public void resolveParameterizedTypeTest5() throws ResolverException {
       test(1, "field", "field", 8, 0, 3, ResolveResultType.FIELD, null);
    }
    @Test 
    public void resolveParameterizedTypeTest6() throws ResolverException {
       test(1, "T", "methodFromIBound3", 7, 0, 0, ResolveResultType.METHOD, null);
    }
    @Test 
    public void resolveParameterizedTypeTest4() throws ResolverException {
       test(2, "field", "equals", 0, 0, 0, ResolveResultType.METHOD, null, true);
    }
    @Test
    public void resolveNotExistantIASTNode() throws ResolverException {
       final IResolver resolver = new Resolver();
       ResolveResult result = null;

       result = resolver.resolve(cuParam2, getIASTNode("somethingThatDoesNotExist", 0, 2));
       
       assertEquals(null, result);
    }
    @Test
    public void resolveArrayCloneMethod() throws ResolverException {
       test(0, "arrayField3", "equals", 0, 0, 0, ResolveResultType.METHOD, null, true);
    }
    @Test(expected=ResolverException.class)
    public void resolveMethodResultInInvariant() throws ResolverException {
       final IResolver resolver = new Resolver();
       
       resolver.resolve(cuParam2, getIASTNode("\\result", 0, 2));
    }
    //********************************************************************************************

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
    
    private static IASTNode getIASTNode(final String identifier, int skip, final int testFile) {
        final List<IASTNode> list = new ArrayList<IASTNode>();
        
        List<IASTNode> testList = null;
        switch(testFile) {
           case 0:
              testList = iASTList;
              break;
           case 1:
              testList = iASTListParam;
              break;
           case 2:
              testList = iASTListParam2;
              break;
           default:
              return null;
        }
        
        for(final IASTNode jml : testList) {
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
            if(node.getChildren().get(0).getChildren().get(0).getType() == NodeTypes.KEYWORD) {
               if(((IKeywordNode)node.getChildren().get(0).getChildren().get(0)).getKeywordInstance().equals(identifier)) {
                  if(skip-- == 0) {
                      return node;
                  }
              }
            }
            if(node.getChildren().get(0).getType() == ExpressionNodeTypes.CAST 
            && node.getChildren().get(0).getChildren().get(0).getType() == ExpressionNodeTypes.REFERENCE_TYPE 
            && node.getChildren().get(0).getChildren().get(0).getChildren().get(0).getChildren().get(0).getType() == NodeTypes.STRING) {
               if(((IStringNode)node.getChildren().get(0).getChildren().get(0).getChildren().get(0).getChildren().get(0)).getString().equals(identifier)) {
                  if(skip-- == 0) {
                      return node;
                  }
              }
            }
        }
        return null;
    }
    
    /**
     * Helper function for the tests.
     * Finds an IASTNode with the given identifier from the JML comments.
     * @param identifier the {@link String} that is to be searched for in the JML comments
     * @return the {@link IASTNode} that contains the {@link String}
     */
    private static IASTNode getIASTNode(final String identifier, final int skip) {
       return getIASTNode(identifier, skip, 0);
    }
    
    private IASTNode getIASTNodeCast(final String name) {
        final List<IASTNode> list = new ArrayList<IASTNode>();
        
        for(final IASTNode jml : iASTList) {
             list.addAll(Nodes.getAllNodesOfType(jml, ExpressionNodeTypes.PRIMARY_EXPR));
        }
        
        
        for(final IASTNode node : list) {
            if(node.getChildren().get(0).getType() == ExpressionNodeTypes.CAST) {
                if(node.getChildren().get(0).getChildren().get(0).getChildren().get(0).getChildren().size() > 0 &&
                      ((IStringNode)node.getChildren().get(0).getChildren().get(0).getChildren().get(0).getChildren().get(0)).getString().equals(name)) {
                   return node;
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
