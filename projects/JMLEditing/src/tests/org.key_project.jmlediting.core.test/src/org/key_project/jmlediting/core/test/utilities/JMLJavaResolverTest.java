package org.key_project.jmlediting.core.test.utilities;

import static org.junit.Assert.assertEquals;

import java.util.List;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.TypeDeclaration;
import org.eclipse.jdt.core.search.IJavaSearchConstants;
import org.eclipse.jdt.core.search.IJavaSearchScope;
import org.eclipse.jdt.core.search.SearchEngine;
import org.eclipse.jdt.core.search.SearchMatch;
import org.eclipse.jdt.core.search.SearchParticipant;
import org.eclipse.jdt.core.search.SearchPattern;
import org.eclipse.jdt.core.search.SearchRequestor;
import org.eclipse.jdt.ui.SharedASTProvider;
import org.junit.After;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.core.test.Activator;
import org.key_project.jmlediting.core.utilities.JMLJavaResolver;
import org.key_project.jmlediting.core.utilities.TypeDeclarationFinder;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.test.util.TestUtilsUtil;

public class JMLJavaResolverTest {
   private final int FIRSTCLASS_ALL_VISIBLE = 8;
   private final int SECONDCLASS_ALL_VISIBLE = 6;
   private final int SUPERCLASS_ALL_VISIBLE = 4;
   private final int NESTEDFIRSTCLASS_ALL_VISIBLE = 12;
   private final int NESTEDSECONDCLASS_ALL_VISIBLE = 10;
   private final int NESTEDSUPERCLASS_ALL_VISIBLE = 8;
   private final int FIRSTCLASS_SECONDREF_ALL_VISIBLE = 3;

   @BeforeClass
   public static void beforeClass() throws Exception {
      System.out
            .println("________________________begin________________________");

      final IJavaProject project = TestUtilsUtil
            .createJavaProject("TestProject");
      final IFolder srcFolder = project.getProject().getFolder("src");
      final IFolder testFolder = TestUtilsUtil.createFolder(srcFolder, "test");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID,
            "data/template/resolverTest", testFolder);
   }

   private class OwnRequestor extends SearchRequestor {
      private final String name;
      private ITypeBinding declaringType = null;
      private ITypeBinding activeType = null;

      public OwnRequestor(final String name) {
         this.name = name;
      }

      @Override
      public void acceptSearchMatch(final SearchMatch match)
            throws CoreException {
         final ICompilationUnit cu = (ICompilationUnit) JavaCore.create(match
               .getResource());
         final org.eclipse.jdt.core.dom.CompilationUnit ast = SharedASTProvider
               .getAST(cu, SharedASTProvider.WAIT_YES, null);

         final TypeDeclarationFinder finder = new TypeDeclarationFinder();
         ast.accept(finder);
         final List<TypeDeclaration> decls = finder.getDecls();
         final TypeDeclaration topDecl = decls.get(0);

         this.declaringType = topDecl.resolveBinding();

         for (final TypeDeclaration decl : decls) {
            if (decl.getName().toString().equals(this.name)) {
               this.activeType = decl.resolveBinding();
            }
         }
      }

      public ITypeBinding getDeclaringType() {
         return this.declaringType;
      }

      public ITypeBinding getActiveType() {
         return this.activeType;
      }

   }

   private ITypeBinding[] getTypeBindingFor(final String name) throws Exception {
      final IJavaSearchScope searchScope = SearchEngine.createWorkspaceScope();
      final SearchEngine searchEngine = new SearchEngine();
      final SearchPattern searchPattern = SearchPattern.createPattern(name,
            IJavaSearchConstants.TYPE, IJavaSearchConstants.DECLARATIONS,
            SearchPattern.R_EXACT_MATCH);
      final OwnRequestor requestor = new OwnRequestor(name);

      searchEngine.search(searchPattern, new SearchParticipant[] { SearchEngine
            .getDefaultSearchParticipant() }, searchScope, requestor, null);

      final ITypeBinding[] result = new ITypeBinding[2];
      result[0] = requestor.getDeclaringType();
      result[1] = requestor.getActiveType();

      return result;
   }

   @AfterClass
   public static void afterClass() {
      System.out
            .println("_________________________end_________________________");
   }

   @After
   public void after() {
      JMLJavaResolver.debugVisibility = false;
   }

   @Test
   public void testGetAllVisibleVariablesFirstClass() throws Exception {
      final ITypeBinding[] firstClassTypes = this
            .getTypeBindingFor("FirstClass");
      final JMLJavaResolver resolver = new JMLJavaResolver(firstClassTypes[0],
            firstClassTypes[1]);

      assertEquals("Not the right amount of visible Variables was found",
            this.FIRSTCLASS_ALL_VISIBLE, resolver
                  .getAllVisibleVariableBindings().size());
   }

   @Test
   public void testGetAllVisibleVariablesSecondClass() throws Exception {
      final ITypeBinding[] secondClassTypes = this
            .getTypeBindingFor("SecondClass");
      final JMLJavaResolver resolver = new JMLJavaResolver(secondClassTypes[0],
            secondClassTypes[1]);

      assertEquals("Not the right amount of visible Variables was found",
            this.SECONDCLASS_ALL_VISIBLE, resolver
                  .getAllVisibleVariableBindings().size());
   }

   @Test
   public void testGetAllVisibleVariablesSuperClass() throws Exception {
      final ITypeBinding[] superClassTypes = this
            .getTypeBindingFor("SuperClass");
      final JMLJavaResolver resolver = new JMLJavaResolver(superClassTypes[0],
            superClassTypes[1]);

      assertEquals("Not the right amount of visible Variables was found",
            this.SUPERCLASS_ALL_VISIBLE, resolver
                  .getAllVisibleVariableBindings().size());
   }

   @Test
   public void testGetAllVisibleVariablesNestedFirstClass() throws Exception {
      final ITypeBinding[] nestedInFirstClassTypes = this
            .getTypeBindingFor("NestedInFirstClass");
      final JMLJavaResolver resolver = new JMLJavaResolver(
            nestedInFirstClassTypes[0], nestedInFirstClassTypes[1]);

      assertEquals("Not the right amount of visible Variables was found",
            this.NESTEDFIRSTCLASS_ALL_VISIBLE, resolver
                  .getAllVisibleVariableBindings().size());
   }

   @Test
   public void testGetAllVisibleVariablesNestedSecondClass() throws Exception {
      final ITypeBinding[] nestedInSecondClassTypes = this
            .getTypeBindingFor("NestedInSecondClass");
      final JMLJavaResolver resolver = new JMLJavaResolver(
            nestedInSecondClassTypes[0], nestedInSecondClassTypes[1]);

      assertEquals("Not the right amount of visible Variables was found",
            this.NESTEDSECONDCLASS_ALL_VISIBLE, resolver
                  .getAllVisibleVariableBindings().size());
   }

   @Test
   public void testGetAllVisibleVariablesNestedSuperClass() throws Exception {
      final ITypeBinding[] nestedInSuperClassTypes = this
            .getTypeBindingFor("NestedInSuperClass");
      final JMLJavaResolver resolver = new JMLJavaResolver(
            nestedInSuperClassTypes[0], nestedInSuperClassTypes[1]);

      assertEquals("Not the right amount of visible Variables was found",
            this.NESTEDSUPERCLASS_ALL_VISIBLE, resolver
                  .getAllVisibleVariableBindings().size());
   }

   @Test
   public void resolveSecondRefFromFirstClassAndGetAllVariables()
         throws Exception {
      final ITypeBinding[] firstClassTypes = this
            .getTypeBindingFor("FirstClass");

      final JMLJavaResolver firstResolver = new JMLJavaResolver(
            firstClassTypes[0], firstClassTypes[1]);

      final ITypeBinding secondClassBinding = firstResolver
            .getTypeForName("secondClassRef");

      JMLJavaResolver.debugVisibility = true;
      final JMLJavaResolver secondResolver = new JMLJavaResolver(
            firstClassTypes[0], secondClassBinding);

      assertEquals("Not the right amount of visible Variables was found",
            this.FIRSTCLASS_SECONDREF_ALL_VISIBLE, secondResolver
                  .getAllVisibleVariableBindings().size());

   }
}
