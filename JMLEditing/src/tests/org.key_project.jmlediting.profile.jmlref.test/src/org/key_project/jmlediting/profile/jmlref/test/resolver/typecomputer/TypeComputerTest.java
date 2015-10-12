package org.key_project.jmlediting.profile.jmlref.test.resolver.typecomputer;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;

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
import org.key_project.jmlediting.core.parser.IJMLParser;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.resolver.typecomputer.TypeComputer;
import org.key_project.jmlediting.core.resolver.typecomputer.TypeComputerException;
import org.key_project.jmlediting.core.utilities.CommentLocator;
import org.key_project.jmlediting.core.utilities.CommentRange;
import org.key_project.jmlediting.core.utilities.LogUtil;
import org.key_project.jmlediting.profile.jmlref.resolver.typecomputer.JMLTypeComputer;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionNodeTypes;
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
      for (final CommentRange jmlCommentRange : CommentLocator.listJMLCommentRanges(icu.getSource())) {
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
      
      final IASTNode node = getIASTNode(type, commentNr);
      assertNotEquals(null, node);
      
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
      
      return findNode(node, type);
   }
   
   private IASTNode findNode(final IASTNode node, final int type) {
      if(node.getType() == type) {
         return node;
      }
      for(final IASTNode child : node.getChildren()) {
         final IASTNode result = findNode(child, type);
         if(result != null) {
            return result;
         }
      }
      return null;
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
      assertEquals("float" , result.getQualifiedName());
      assertTrue(cu.getAST().resolveWellKnownType("float").isEqualTo(result));
   }
   
   @Test
   public void ExpressionNodeTypesMULT2() throws TypeComputerException {
      
      final ITypeBinding result = test(0, ExpressionNodeTypes.MULT, 8);
      
      assertNotEquals(null, result);
      assertEquals("int" , result.getQualifiedName());
      assertTrue(cu.getAST().resolveWellKnownType("int").isEqualTo(result));
   }
   
   @Test
   public void ExpressionNodeTypesEQUIVALENCE_OP() throws TypeComputerException {
      
      final ITypeBinding result = test(0, ExpressionNodeTypes.EQUIVALENCE_OP, 9);
      
      assertNotEquals(null, result);
      assertEquals("boolean" , result.getQualifiedName());
      assertTrue(cu.getAST().resolveWellKnownType("boolean").isEqualTo(result));
   }
   
   // ************************************************************************
   
   @Test
   public void ExpressionNodeTypesIMPLIES() throws TypeComputerException {
      
      final ITypeBinding result = test(0, ExpressionNodeTypes.IMPLIES, 10);
      
      assertNotEquals(null, result);
      assertEquals("boolean" , result.getQualifiedName());
      assertTrue(cu.getAST().resolveWellKnownType("boolean").isEqualTo(result));
   }
   
   @Test
   public void ExpressionNodeTypesNOT() throws TypeComputerException {
      
      final ITypeBinding result = test(0, ExpressionNodeTypes.NOT, 11);
      
      assertNotEquals(null, result);
      assertEquals("boolean" , result.getQualifiedName());
      assertTrue(cu.getAST().resolveWellKnownType("boolean").isEqualTo(result));
   }
   
   @Test
   public void ExpressionNodeTypesCAST() throws TypeComputerException {
      
      final ITypeBinding result = test(0, ExpressionNodeTypes.CAST, 12);
      
      assertNotEquals(null, result);
      assertEquals("java.lang.Object" , result.getQualifiedName());
      assertTrue(cu.getAST().resolveWellKnownType("java.lang.Object").isEqualTo(result));
   }
   
   @Test
   public void ExpressionNodeTypesRELATIONAL_OP() throws TypeComputerException {
      
      final ITypeBinding result = test(0, ExpressionNodeTypes.RELATIONAL_OP, 13);
      
      assertNotEquals(null, result);
      assertEquals("boolean" , result.getQualifiedName());
      assertTrue(cu.getAST().resolveWellKnownType("boolean").isEqualTo(result));
   }
   
   @Test
   public void ExpressionNodeTypesPREFIX_INCREMENT() throws TypeComputerException {
      
      final ITypeBinding result = test(0, ExpressionNodeTypes.PREFIX_INCREMENT, 14);
      
      assertNotEquals(null, result);
      assertEquals("int" , result.getQualifiedName());
      assertTrue(cu.getAST().resolveWellKnownType("int").isEqualTo(result));
   }
   
   @Test
   public void ExpressionNodeTypesPOST_FIX_EXPR() throws TypeComputerException {
      
      final ITypeBinding result = test(0, ExpressionNodeTypes.POST_FIX_EXPR, 15);
      
      assertNotEquals(null, result);
      assertEquals("int" , result.getQualifiedName());
      assertTrue(cu.getAST().resolveWellKnownType("int").isEqualTo(result));
   }
   
   @Test
   public void ExpressionNodeTypesADDITIVE1() throws TypeComputerException {
      
      final ITypeBinding result = test(0, ExpressionNodeTypes.ADDITIVE, 16);
      
      assertNotEquals(null, result);
      assertEquals("int" , result.getQualifiedName());
      assertTrue(cu.getAST().resolveWellKnownType("int").isEqualTo(result));
   }
   
   @Test
   public void ExpressionNodeTypesADDITIVE2() throws TypeComputerException {
      
      final ITypeBinding result = test(0, ExpressionNodeTypes.ADDITIVE, 17);
      
      assertNotEquals(null, result);
      assertEquals("float" , result.getQualifiedName());
      assertTrue(cu.getAST().resolveWellKnownType("float").isEqualTo(result));
   }
   
   @Test
   public void ExpressionNodeTypesLOGICAL_AND() throws TypeComputerException {
      
      final ITypeBinding result = test(0, ExpressionNodeTypes.LOGICAL_AND, 18);
      
      assertNotEquals(null, result);
      assertEquals("boolean" , result.getQualifiedName());
      assertTrue(cu.getAST().resolveWellKnownType("boolean").isEqualTo(result));
   }
   
   @Test
   public void ExpressionNodeTypesLOGICAL_OR() throws TypeComputerException {
      
      final ITypeBinding result = test(0, ExpressionNodeTypes.LOGICAL_OR, 19);
      
      assertNotEquals(null, result);
      assertEquals("boolean" , result.getQualifiedName());
      assertTrue(cu.getAST().resolveWellKnownType("boolean").isEqualTo(result));
   }
   
   // ***************************************************************************
   
   @Test
   public void ExpressionNodeTypesBINARY_AND() throws TypeComputerException {
      
      final ITypeBinding result = test(0, ExpressionNodeTypes.BINARY_AND, 20);
      
      assertNotEquals(null, result);
      assertEquals("boolean" , result.getQualifiedName());
      assertTrue(cu.getAST().resolveWellKnownType("boolean").isEqualTo(result));
   }
   
   @Test
   public void ExpressionNodeTypesBINARY_EXCLUSIVE_OR() throws TypeComputerException {
      
      final ITypeBinding result = test(0, ExpressionNodeTypes.BINARY_EXCLUSIVE_OR, 21);
      
      assertNotEquals(null, result);
      assertEquals("boolean" , result.getQualifiedName());
      assertTrue(cu.getAST().resolveWellKnownType("boolean").isEqualTo(result));
   }
   
   @Test
   public void ExpressionNodeTypesBINARY_OR() throws TypeComputerException {
      
      final ITypeBinding result = test(0, ExpressionNodeTypes.BINARY_OR, 22);
      
      assertNotEquals(null, result);
      assertEquals("boolean" , result.getQualifiedName());
      assertTrue(cu.getAST().resolveWellKnownType("boolean").isEqualTo(result));
   }
   
   @Test
   public void ExpressionNodeTypesSHIFT1() throws TypeComputerException {
      
      final ITypeBinding result = test(0, ExpressionNodeTypes.SHIFT, 23);
      
      assertNotEquals(null, result);
      assertEquals("int" , result.getQualifiedName());
      assertTrue(cu.getAST().resolveWellKnownType("int").isEqualTo(result));
   }
   
   @Test
   public void ExpressionNodeTypesSHIFT2() throws TypeComputerException {
      
      final ITypeBinding result = test(0, ExpressionNodeTypes.SHIFT, 24);
      
      assertNotEquals(null, result);
      assertEquals("float" , result.getQualifiedName());
      assertTrue(cu.getAST().resolveWellKnownType("float").isEqualTo(result));
   }
   
   @Test
   public void ExpressionNodeTypesPREFIX_DECREMENT() throws TypeComputerException {
      
      final ITypeBinding result = test(0, ExpressionNodeTypes.PREFIX_DECREMENT, 25);
      
      assertNotEquals(null, result);
      assertEquals("float" , result.getQualifiedName());
      assertTrue(cu.getAST().resolveWellKnownType("float").isEqualTo(result));
   }
   
   @Test
   public void ExpressionNodeTypesTILDE() throws TypeComputerException {
      
      final ITypeBinding result = test(0, ExpressionNodeTypes.TILDE, 26);
      
      assertNotEquals(null, result);
      assertEquals("int" , result.getQualifiedName());
      assertTrue(cu.getAST().resolveWellKnownType("int").isEqualTo(result));
   }
   
   @Test
   public void ExpressionNodeTypesPLUS() throws TypeComputerException {
      
      final ITypeBinding result = test(0, ExpressionNodeTypes.PLUS, 27);
      
      assertNotEquals(null, result);
      assertEquals("float" , result.getQualifiedName());
      assertTrue(cu.getAST().resolveWellKnownType("float").isEqualTo(result));
   }
   
   @Test
   public void ExpressionNodeTypesNEW_EXPRESSION() throws TypeComputerException {
      
      final ITypeBinding result = test(0, ExpressionNodeTypes.NEW_EXPRESSION, 28);
      
      assertNotEquals(null, result);
      assertEquals("java.lang.Boolean" , result.getQualifiedName());
      assertTrue(cu.getAST().resolveWellKnownType("java.lang.Boolean").isEqualTo(result));
   }
   
   @Test
   public void ExpressionNodeTypesASSIGNMENT1() throws TypeComputerException {
      
      // take the type of the left part of the assignment and return its type.
      final ITypeBinding result = test(0, ExpressionNodeTypes.ASSIGNMENT, 29);
      
      assertNotEquals(null, result);
      assertEquals("java.lang.Object" , result.getQualifiedName());
      assertTrue(cu.getAST().resolveWellKnownType("java.lang.Object").isEqualTo(result));
   }
   
   //*********************************************************************************
   
   @Test
   public void ExpressionNodeTypesASSIGNMENT2() throws TypeComputerException {
      
      // take the type of the left part of the assignment and return its type.
      final ITypeBinding result = test(0, ExpressionNodeTypes.ASSIGNMENT, 30);
      
      assertNotEquals(null, result);
      assertEquals("java.lang.String" , result.getQualifiedName());
      assertTrue(cu.getAST().resolveWellKnownType("java.lang.String").isEqualTo(result));
   }
   
   @Test
   public void ExpressionNodeTypesMINUS() throws TypeComputerException {
      
      final ITypeBinding result = test(0, ExpressionNodeTypes.MINUS, 31);
      
      assertNotEquals(null, result);
      assertEquals("double" , result.getQualifiedName());
      assertTrue(cu.getAST().resolveWellKnownType("double").isEqualTo(result));
   }
   
   @Test(expected = TypeComputerException.class)
   public void UnrecognisedNodeType() throws TypeComputerException {
      
      final TypeComputer tc = new JMLTypeComputer(icu);
      
      tc.computeType(new IASTNode() {
         
         @Override
         public <T> T traverse(final INodeTraverser<T> traverser, final T init) {
            return null;
         }
         
         @Override
         public <T> T search(final INodeSearcher<T> searcher) {
            return null;
         }
         
         @Override
         public String prettyPrintAST() {
            return "ThisNodeDoesNotExist";
         }
         
         @Override
         public int getType() {
            return 0;
         }
         
         @Override
         public int getStartOffset() {
            return 0;
         }
         
         @Override
         public int getEndOffset() {
            return 0;
         }
         
         @Override
         public List<IASTNode> getChildren() {
            return new LinkedList<IASTNode>();
         }
         
         @Override
         public boolean containsOffset(final int offset) {
            return false;
         }
         
         @Override
         public boolean containsCaret(final int caretPosition) {
            return false;
         }
      });
   }
   
   @Test
   public void ExpressionNodeTypesPRIMARY_EXPR2() throws TypeComputerException {
      
      final ITypeBinding result = test(0, ExpressionNodeTypes.PRIMARY_EXPR, 32);
      
      assertNotEquals(null, result);
      assertEquals("boolean" , result.getQualifiedName());
      assertTrue(cu.getAST().resolveWellKnownType("boolean").isEqualTo(result));
   }
   
   
   
   
   
   
   
   
}
