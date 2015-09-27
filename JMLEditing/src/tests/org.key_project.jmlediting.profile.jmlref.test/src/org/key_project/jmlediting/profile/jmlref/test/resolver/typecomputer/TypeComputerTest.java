package org.key_project.jmlediting.profile.jmlref.test.resolver.typecomputer;

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
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.INodeSearcher;
import org.key_project.jmlediting.core.dom.INodeTraverser;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.parser.IJMLParser;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.parser.util.JavaBasicsNodeTypes;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.resolver.IResolver;
import org.key_project.jmlediting.core.resolver.ResolveResult;
import org.key_project.jmlediting.core.resolver.ResolverException;
import org.key_project.jmlediting.core.resolver.typecomputer.TypeComputer;
import org.key_project.jmlediting.core.resolver.typecomputer.TypeComputerException;
import org.key_project.jmlediting.core.utilities.CommentLocator;
import org.key_project.jmlediting.core.utilities.CommentRange;
import org.key_project.jmlediting.core.utilities.LogUtil;
import org.key_project.jmlediting.profile.jmlref.quantifier.QuantifierNodeTypes;
import org.key_project.jmlediting.profile.jmlref.resolver.Resolver;
import org.key_project.jmlediting.profile.jmlref.resolver.typecomputer.JMLTypeComputer;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionNodeTypes;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.StoreRefNodeTypes;
import org.key_project.jmlediting.profile.jmlref.test.Activator;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.jdt.JDTUtil;
import org.key_project.util.test.util.TestUtilsUtil;

public class TypeComputerTest {
   
   private static final String PATH = "src/typecomputer/test/";
   private static final String FILE1 = "Test1";
   private static List<IASTNode> iASTList = new LinkedList<IASTNode>();
   private static IJavaProject javaProject;
   private static IFolder srcFolder;
   private static IFolder testFolder;
   private static ICompilationUnit icu;
   private static ASTNode cu;

   @BeforeClass
   public static void initProject() throws CoreException, InterruptedException {
      javaProject = TestUtilsUtil.createJavaProject("TypeComputerTest");
      srcFolder = javaProject.getProject().getFolder(JDTUtil.getSourceFolderName());
      testFolder = TestUtilsUtil.createFolder(srcFolder, "typecomputer");
      testFolder = TestUtilsUtil.createFolder(testFolder, "test");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data\\template\\typecomputerTest", testFolder);
      TestUtilsUtil.waitForBuild();
      JMLPreferencesHelper.setProjectJMLProfile(javaProject.getProject(), JMLPreferencesHelper.getDefaultJMLProfile());
      
      icu = (ICompilationUnit) JavaCore.create(javaProject.getProject().getFile(PATH+FILE1+JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
      cu = JDTUtil.parse(icu);
      
      // Parse JML
      final IJMLParser parser = JMLPreferencesHelper.getProjectJMLProfile(javaProject.getProject()).createParser();
      final CommentLocator locator = new CommentLocator(icu.getSource());
      for (final CommentRange jmlCommentRange : locator.findJMLCommentRanges()) {
          try {
              iASTList.add(parser.parse(icu.getSource(), jmlCommentRange));
          }
          catch (final ParserException e) {
              LogUtil.getLogger().logError(e);
          }
      }
   }
   
   private ITypeBinding test(final int file, final int type, final int commentNr) throws TypeComputerException {
      
      ICompilationUnit compUnit = null;
      switch(file) {
      case 0:
         compUnit = icu;
         break;
      default:
         return null;
      }
      
      final TypeComputer tc = new JMLTypeComputer(compUnit);
      
      //JavaBasicsNodeTypes.BOOLEAN_LITERAL
      final IASTNode node = getIASTNode(type, commentNr);
      
      final ITypeBinding result = tc.computeType(node);
      return result;
   }
   /*
    * ExpressionNodeTypes
    * NodeTypes
    * JavaBasicsNodeTypes
    * QuantifierNodeTypes
    * StoreRefNodeTypes
    */
   /** 
    * Returns the first found instance with the given {code type} in comment number {@code commentNr}.
    * @param type the node type to be found
    * @param commentNr the comment to search in
    * @return the first found instance with matching type
    */
   private IASTNode getIASTNode(final int type, final int commentNr) {      
      if(commentNr < 0 || commentNr >= iASTList.size()) {
         return null;
      }
      
      final IASTNode node = iASTList.get(commentNr);
      
      return node.traverse(new INodeTraverser<IASTNode>() {

         @Override
         public IASTNode traverse(final IASTNode node, final IASTNode existing) {
            if(node.getType() == type && existing == null) {
               return node;
            }
            return existing;
         }
         
      }, null);
   }
   
   // ***************************************************************************
   // *                            TESTS START HERE                             *
   // ***************************************************************************
   @Test
   public void JavaBasicsNodeTypesBOOLEAN_LITERAL() throws TypeComputerException {
      
      final ITypeBinding result = test(0, ExpressionNodeTypes.PRIMARY_EXPR, 0);
      
      assertNotEquals(null, result);
      assertEquals("boolean" , result.getQualifiedName());
      assertTrue(cu.getAST().resolveWellKnownType("boolean").isEqualTo(result));
   }
   
   @Test
   public void JavaBasicsNodeTypesCHARACTER_LITERAL() throws TypeComputerException {
      
      final ITypeBinding result = test(0, ExpressionNodeTypes.PRIMARY_EXPR, 1);
      
      assertNotEquals(null, result);
      assertEquals("char" , result.getQualifiedName());
      assertTrue(cu.getAST().resolveWellKnownType("char").isEqualTo(result));
   }
   
   @Test
   public void JavaBasicsNodeTypesINTEGER_LITERAL() throws TypeComputerException {
      
      final ITypeBinding result = test(0, ExpressionNodeTypes.PRIMARY_EXPR, 2);
      
      assertNotEquals(null, result);
      assertEquals("int" , result.getQualifiedName());
      assertTrue(cu.getAST().resolveWellKnownType("int").isEqualTo(result));
   }
   
   @Test
   public void JavaBasicsNodeTypesSTRING_LITERAL() throws TypeComputerException {
      
      final ITypeBinding result = test(0, ExpressionNodeTypes.PRIMARY_EXPR, 3);
      
      assertNotEquals(null, result);
      assertEquals("java.lang.String" , result.getQualifiedName());
      assertTrue(cu.getAST().resolveWellKnownType("java.lang.String").isEqualTo(result));
   }
   
   @Test
   public void ExpressionNodeTypesEQUALITY() throws TypeComputerException {

      final ITypeBinding result = test(0, ExpressionNodeTypes.EQUALITY, 4);
      
      assertNotEquals(null, result);
      assertEquals("boolean" , result.getQualifiedName());
      assertTrue(cu.getAST().resolveWellKnownType("boolean").isEqualTo(result));
   }
   
   @Test
   public void ExpressionNodeTypesPRIMARY_EXPR() throws TypeComputerException {

      final ITypeBinding result = test(0, ExpressionNodeTypes.PRIMARY_EXPR, 5);
            
      assertNotEquals(null, result);
      assertEquals("boolean" , result.getQualifiedName());
   }

   @Test
   public void JavaBasicsNodeTypesFLOAT_LITERAL() throws TypeComputerException {
      
      final ITypeBinding result = test(0, ExpressionNodeTypes.PRIMARY_EXPR, 6);
      
      assertNotEquals(null, result);
      assertEquals("float" , result.getQualifiedName());
      assertTrue(cu.getAST().resolveWellKnownType("float").isEqualTo(result));
   }
   
   @Test
   public void ExpressionNodeTypesMULT1() throws TypeComputerException {
      
      final ITypeBinding result = test(0, ExpressionNodeTypes.MULT, 7);
      
      assertNotEquals(null, result);
      assertEquals("double" , result.getQualifiedName());
      assertTrue(cu.getAST().resolveWellKnownType("double").isEqualTo(result));
   }
   
   @Test
   public void ExpressionNodeTypesMULT2() throws TypeComputerException {
      
      final ITypeBinding result = test(0, ExpressionNodeTypes.MULT, 8);
      
      assertNotEquals(null, result);
      assertEquals("int" , result.getQualifiedName());
      assertTrue(cu.getAST().resolveWellKnownType("int").isEqualTo(result));
   }
   
   
}
