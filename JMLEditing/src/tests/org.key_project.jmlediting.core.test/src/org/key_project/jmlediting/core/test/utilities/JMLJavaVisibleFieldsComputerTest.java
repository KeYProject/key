package org.key_project.jmlediting.core.test.utilities;

import static org.junit.Assert.assertEquals;

import java.util.List;

import org.eclipse.core.resources.IFolder;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.dom.AST;
import org.eclipse.jdt.core.dom.ASTParser;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.TypeDeclaration;
import org.junit.After;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.core.test.Activator;
import org.key_project.jmlediting.core.utilities.JMLJavaVisibleFieldsComputer;
import org.key_project.jmlediting.core.utilities.TypeDeclarationFinder;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.jdt.JDTUtil;
import org.key_project.util.test.util.TestUtilsUtil;

public class JMLJavaVisibleFieldsComputerTest {

   private static IJavaProject project;

   private static ITypeBinding firstClass;
   private static ITypeBinding nestedInFirstClass;
   private static ITypeBinding superClass;
   private static ITypeBinding nestedInSuperClass;

   @BeforeClass
   public static void beforeClass() throws Exception {
      project = TestUtilsUtil.createJavaProject("TestProject");
      final IFolder srcFolder = project.getProject().getFolder("src");
      final IFolder testFolder = TestUtilsUtil.createFolder(srcFolder, "test");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID,
            "data/template/resolverTest", testFolder);
      firstClass = getTypeBinding("src/test/FirstClass", 0);
      nestedInFirstClass = getTypeBinding("src/test/FirstClass", 1);
      superClass = getTypeBinding("src/test/SuperClass", 0);
      nestedInSuperClass = getTypeBinding("src/test/SuperClass", 1);

   }

   public static ITypeBinding getTypeBinding(final String file, final int num) {
      final ICompilationUnit cu = (ICompilationUnit) JavaCore.create(project
            .getProject().getFile(file + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));

      final ASTParser parser = ASTParser.newParser(AST.JLS8);
      parser.setKind(ASTParser.K_COMPILATION_UNIT);
      parser.setSource(cu);
      parser.setResolveBindings(true);
      final org.eclipse.jdt.core.dom.CompilationUnit ast = (org.eclipse.jdt.core.dom.CompilationUnit) parser
            .createAST(null);
      final TypeDeclarationFinder finder = new TypeDeclarationFinder();
      ast.accept(finder);
      final List<TypeDeclaration> decls = finder.getDecls();
      final TypeDeclaration topDecl = decls.get(num);

      return topDecl.resolveBinding();
   }

   @After
   public void after() {
      JMLJavaVisibleFieldsComputer.debugVisibility = false;
   }

   private static int getNumVisibleVarsFor(final ITypeBinding context,
         final ITypeBinding type) {
      return new JMLJavaVisibleFieldsComputer(context)
            .getAllVisibleFields(type).size();
   }

   @Test
   public void testFirstClassInFirstClass() throws Exception {
      assertEquals("Not the right amount of visible Variables was found", 8,
            getNumVisibleVarsFor(firstClass, firstClass));
   }

   @Test
   public void testNestedInFirstClassInFirstClass() throws Exception {
      assertEquals("Not the right amount of visible Variables was found", 4,
            getNumVisibleVarsFor(firstClass, nestedInFirstClass));
   }

   @Test
   public void testSuperClassInSuperClass() throws Exception {
      assertEquals("Not the right amount of visible Variables was found", 4,
            getNumVisibleVarsFor(superClass, superClass));
   }

   @Test
   public void testNestedInFirstClassInSuperClass() throws Exception {
      assertEquals("Not the right amount of visible Variables was found", 3,
            getNumVisibleVarsFor(superClass, nestedInFirstClass));
   }

   @Test
   public void testSuperClassInNestedInFirstClass() throws Exception {
      assertEquals("Not the right amount of visible Variables was found", 3,
            getNumVisibleVarsFor(nestedInFirstClass, superClass));
   }

   @Test
   public void testSuperClassInFirstClass() throws Exception {
      assertEquals("Not the right amount of visible Variables was found", 3,
            getNumVisibleVarsFor(firstClass, superClass));
   }

   @Test
   public void testFirstClassInNestedInSuperClass() throws Exception {
      assertEquals("Not the right amount of visible Variables was found", 7,
            getNumVisibleVarsFor(nestedInSuperClass, firstClass));
   }

   @Test
   public void testNestedInFirstClassInNestedInSuperClass() throws Exception {
      assertEquals("Not the right amount of visible Variables was found", 3,
            getNumVisibleVarsFor(nestedInSuperClass, nestedInFirstClass));
   }

   @Test
   public void resolveSecondRefFromFirstClassAndGetAllVariables()
         throws Exception {
      final JMLJavaVisibleFieldsComputer firstResolver = new JMLJavaVisibleFieldsComputer(
            firstClass);

      final ITypeBinding secondClassBinding = firstResolver.getTypeForName(
            firstClass, "secondClassRef");

      JMLJavaVisibleFieldsComputer.debugVisibility = true;
      final JMLJavaVisibleFieldsComputer secondResolver = new JMLJavaVisibleFieldsComputer(
            firstClass);

      assertEquals("Not the right amount of visible Variables was found", 4,
            secondResolver.getAllVisibleFields(secondClassBinding).size());

   }
}
