package org.key_project.stubby.core.test.testcase;

import java.io.File;
import java.io.IOException;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import junit.framework.TestCase;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.ResourceSet;
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.dom.ASTNode;
import org.junit.Test;
import org.key_project.stubby.core.generator.StubGeneratorUtil;
import org.key_project.stubby.core.test.Activator;
import org.key_project.stubby.model.dependencymodel.AbstractType;
import org.key_project.stubby.model.dependencymodel.ArrayType;
import org.key_project.stubby.model.dependencymodel.Datatype;
import org.key_project.stubby.model.dependencymodel.DependencyModel;
import org.key_project.stubby.model.dependencymodel.Field;
import org.key_project.stubby.model.dependencymodel.GenericType;
import org.key_project.stubby.model.dependencymodel.Method;
import org.key_project.stubby.model.dependencymodel.Type;
import org.key_project.stubby.model.dependencymodel.TypeVariable;
import org.key_project.stubby.model.dependencymodel.WildcardType;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.StringUtil;
import org.key_project.util.jdt.JDTUtil;
import org.key_project.util.test.util.TestUtilsUtil;
import org.osgi.framework.Bundle;

/**
 * Tests for {@link StubGeneratorUtil}
 * @author Martin Hentschel
 */
public class StubGeneratorUtilTest extends TestCase {
   /**
    * <p>
    * If this constant is {@code true} a temporary directory is created with
    * new oracle files. The developer has than to copy the new required files
    * into the plug-in so that they are used during next test execution.
    * </p>
    * <p>
    * <b>Attention: </b> It is strongly required that new test scenarios
    * are verified with the SED application. If everything is fine a new test
    * method can be added to this class and the first test execution can be
    * used to generate the required oracle file. Existing oracle files should
    * only be replaced if the functionality of the Symbolic Execution Debugger
    * has changed so that they are outdated.
    * </p>
    */
   public static final boolean CREATE_NEW_ORACLE_FILES_IN_TEMP_DIRECTORY = false;
   
   /**
    * The used temporary oracle directory.
    */
   private static final File oracleDirectory;

   /**
    * Creates the temporary oracle directory if required.
    */
   static {
      File directory = null;
      try {
         if (CREATE_NEW_ORACLE_FILES_IN_TEMP_DIRECTORY) {
            directory = IOUtil.createTempDirectory("ORACLE_DIRECTORY", StringUtil.EMPTY_STRING);
         }
      }
      catch (IOException e) {
      }
      oracleDirectory = directory;
   }

   @Test
   public void testExtractReferences_wildcardTest() throws CoreException, InterruptedException{
      doExtractReferencesTest("JDTUtilTest_testExtractReferences_wildcardTest", 
                              "data/wildcardTest/test",
                              "data/wildcardTest/oracle/Dependencymodel.dependencymodel");
   }
   
   @Test
   public void testStubs_wildcardType() throws Exception {
      doTestStubs("StubGeneratorUtil_testStubs_wildcardType",
                  "data/wildcardTest/test",
                  "data/wildcardTest/oracleStubs");
   }
  
   @Test
   public void testExtractReferences_importTest() throws CoreException, InterruptedException{
      doExtractReferencesTest("JDTUtilTest_testExtractReferences_importTest", 
                              "data/importTest/test",
                              "data/importTest/oracle/Dependencymodel.dependencymodel");
   }
   
   @Test
   public void testStubs_importTest() throws Exception {
      doTestStubs("StubGeneratorUtil_testStubs_importTest",
                  "data/importTest/test",
                  "data/importTest/oracleStubs");
   }

   @Test
   public void testExtractReferences_innerTypeTest() throws CoreException, InterruptedException{
      doExtractReferencesTest("JDTUtilTest_testExtractReferences_innerTypeTest", 
                              "data/innerTypeTest/test",
                              "data/innerTypeTest/oracle/Dependencymodel.dependencymodel");
   }

   @Test
   public void testStubs_innerTypeTest() throws Exception {
      doTestStubs("StubGeneratorUtil_testStubs_innerTypeTest",
                  "data/innerTypeTest/test",
                  "data/innerTypeTest/oracleStubs");
   }
   
   @Test
   public void testExtractReferences_methodCallTest() throws CoreException, InterruptedException{
      doExtractReferencesTest("JDTUtilTest_testGetReferenceMap_methodCallTest", 
                              "data/methodCallTest/test",
                              "data/methodCallTest/oracle/Dependencymodel.dependencymodel");
   }
   
   @Test
   public void testStubs_methodCallTest() throws Exception {
      doTestStubs("StubGeneratorUtil_testStubs_methodCallTest",
                  "data/methodCallTest/test",
                  "data/methodCallTest/oracleStubs");
   }
   
   @Test
   public void testExtractReferences_superMethodCallTest() throws CoreException, InterruptedException {
      doExtractReferencesTest("JDTUtilTest_testGetReferenceMap_superMethodCallTest",
                              "data/superMethodCallTest/test",
                              "data/superMethodCallTest/oracle/Dependencymodel.dependencymodel");
   }
   
   @Test
   public void testStubs_superMethodCallTest() throws Exception {
      doTestStubs("StubGeneratorUtil_testStubs_superMethodCallTest",
                  "data/superMethodCallTest/test",
                  "data/superMethodCallTest/oracleStubs");
   }
   
   @Test
   public void testExtractReferences_implicitSuperMethodCallTest() throws CoreException, InterruptedException {
      doExtractReferencesTest("JDTUtilTest_testGetReferenceMap_implicitSuper",
                              "data/implicitSuperMethodCallTest/test",
                              "data/implicitSuperMethodCallTest/oracle/Dependencymodel.dependencymodel");
   }
   
   @Test
   public void testStubs_implicitSuperMethodCallTest() throws Exception {
      doTestStubs("StubGeneratorUtil_testStubs_implicitSuperMethodCallTest",
                  "data/implicitSuperMethodCallTest/test",
                  "data/implicitSuperMethodCallTest/oracleStubs");
   }
   
   @Test
   public void testExtractReferences_fieldCallTest() throws CoreException, InterruptedException {
      doExtractReferencesTest("JDTUtilTes_testGetReferenceMap_fieldCallTest",
                              "data/fieldCallTest/test",
                              "data/fieldCallTest/oracle/Dependencymodel.dependencymodel"); 
   }
   
   @Test
   public void testStubs_fieldCallTest() throws Exception {
      doTestStubs("StubGeneratorUtil_testStubs_fieldCallTest",
                  "data/fieldCallTest/test",
                  "data/fieldCallTest/oracleStubs");
   }
   
   @Test
   public void testExtractReferences_superFieldCallTest() throws CoreException, InterruptedException {
      doExtractReferencesTest("JDTUtilTest_testGetReferenceMap_superFieldCallTest", 
                              "data/superFieldCallTest/test",
                              "data/superFieldCallTest/oracle/Dependencymodel.dependencymodel");
   }
   
   @Test
   public void testStubs_superFieldCallTest() throws Exception {
      doTestStubs("StubGeneratorUtil_testStubs_superFieldCallTest",
                  "data/superFieldCallTest/test",
                  "data/superFieldCallTest/oracleStubs");
   }
   
   @Test
   public void testExtractReferences_implicitSuperFieldCallTest() throws Exception {
      doExtractReferencesTest("JDTUtilTest_testGetReferenceMap_implicitSuperFieldCallTest", 
                              "data/implicitSuperFieldCallTest/test",
                              "data/implicitSuperFieldCallTest/oracle/Dependencymodel.dependencymodel");
   }
   
   @Test
   public void testStubs_implicitSuperFieldCallTest() throws Exception {
      doTestStubs("StubGeneratorUtil_testStubs_implicitSuperFieldCallTest",
                  "data/implicitSuperFieldCallTest/test",
                  "data/implicitSuperFieldCallTest/oracleStubs");
   }
   
   @Test
   public void testExtractReferences_implicitFieldCallTest() throws Exception {
      doExtractReferencesTest("JDTUtilTest_testGetReferenceMap_implicitFieldCallTest", 
                              "data/implicitFieldCallTest/test",
                              "data/implicitFieldCallTest/oracle/Dependencymodel.dependencymodel");
   }
   
   @Test
   public void testStubs_implicitFieldCallTest() throws Exception {
      doTestStubs("StubGeneratorUtil_testStubs_implicitFieldCallTest",
                  "data/implicitFieldCallTest/test",
                  "data/implicitFieldCallTest/oracleStubs");
   }
   
   @Test
   public void testExtractReferences_nestedFieldCallTest() throws Exception {
      doExtractReferencesTest("JDTUtilTest_testGetReferenceMap_nestedFieldCallTest",
                              "data/nestedFieldCallTest/test",
                              "data/nestedFieldCallTest/oracle/Dependencymodel.dependencymodel"); 
   }
   
   @Test
   public void testStubs_nestedFieldCallTest() throws Exception {
      doTestStubs("StubGeneratorUtil_testStubs_nestedFieldCallTest",
                  "data/nestedFieldCallTest/test",
                  "data/nestedFieldCallTest/oracleStubs");
   }
   
   
   @Test
   public void testExtractReferences_constructorCallTest() throws CoreException, InterruptedException {
      doExtractReferencesTest("JDTUtilTest_testGetReferenceMap_constructorCallTest", 
                              "data/constructorCallTest/test",
                              "data/constructorCallTest/oracle/Dependencymodel.dependencymodel");
   }
   
   @Test
   public void testStubs_constructorCallTest() throws Exception {
      doTestStubs("StubGeneratorUtil_testStubs_constructorCallTest",
                  "data/constructorCallTest/test",
                  "data/constructorCallTest/oracleStubs");
   }
   
   @Test 
   public void testExtractReferences_superConstructorCallTest() throws Exception {
      doExtractReferencesTest("JDTUtilTest_testGetReferenceMap_superConstructorCallTest", 
                              "/data/superConstructorCallTest/test",
                              "data/superConstructorCallTest/oracle/Dependencymodel.dependencymodel");
   }
   
   @Test
   public void testStubs_superConstructorCallTest() throws Exception {
      doTestStubs("StubGeneratorUtil_testStubs_superConstructorCallTest",
                  "/data/superConstructorCallTest/test",
                  "data/superConstructorCallTest/oracleStubs");
   }
   
   @Test
   public void testExtractReferences_implicitSuperConstructorCallTest() throws Exception {
      doExtractReferencesTest("JDTUtilTest_testGetReferenceMap_implicitSuperConstructorCallTest", 
                              "data/implicitSuperConstructorCallTest/test",
                              "data/implicitSuperConstructorCallTest/oracle/Dependencymodel.dependencymodel");
   }
   
   @Test
   public void testStubs_implicitSuperConstructorCallTest() throws Exception {
      doTestStubs("StubGeneratorUtil_testStubs_implicitSuperConstructorCallTest",
                  "data/implicitSuperConstructorCallTest/test",
                  "data/implicitSuperConstructorCallTest/oracleStubs");
   }
   
   @Test
   public void testExtractReferences_innerThisTest() throws CoreException, InterruptedException {
      doExtractReferencesTest("JDTUtilTest_testGetReferenceMap_innerThisTest", 
                              "data/innerThisTest/test",
                              "data/innerThisTest/oracle/Dependencymodel.dependencymodel");
   }
   
   @Test
   public void testStubs_innerThisTest() throws Exception {
      doTestStubs("StubGeneratorUtil_testStubs_innerThisTest",
                  "data/innerThisTest/test",
                  "data/innerThisTest/oracleStubs");
   }
   
   @Test
   public void testExtractReferences_fieldOnMethodCallTeset() throws Exception {
      doExtractReferencesTest("JDTUtilTest_testGetReferenceMap_fieldOnMethodCallTeset", 
                              "data/fieldOnMethodCallTeset/test",
                              "data/fieldOnMethodCallTeset/oracle/Dependencymodel.dependencymodel");
   }
   
   @Test
   public void testStubs_fieldOnMethodCallTeset() throws Exception {
      doTestStubs("StubGeneratorUtil_testStubs_fieldOnMethodCallTeset",
                  "data/fieldOnMethodCallTeset/test",
                  "data/fieldOnMethodCallTeset/oracleStubs");
   }
   
   @Test
   public void testExtractReferences_nestedFieldOnMethodCallTest() throws CoreException, InterruptedException {
      doExtractReferencesTest("JDTUtilTest_testGetReferenceMap_nestedFieldOnMethodCallTeset",
                              "data/nestedFieldOnMethodCallTeset/test",
                              "data/nestedFieldOnMethodCallTeset/oracle/Dependencymodel.dependencymodel");
                              
   }
   
   @Test
   public void testStubs_nestedFieldOnMethodCallTeset() throws Exception {
      doTestStubs("StubGeneratorUtil_testStubs_nestedFieldOnMethodCallTeset",
                  "data/nestedFieldOnMethodCallTeset/test",
                  "data/nestedFieldOnMethodCallTeset/oracleStubs");
   }
   
   @Test 
   public void testExtractReferences_parameterTypesTest() throws CoreException, InterruptedException {
      doExtractReferencesTest("JDTUtilTest_testGetReferenceMap_parameterTypesTest",
                              "data/parameterTypesTest/test", 
                              "data/parameterTypesTest/oracle/Dependencymodel.dependencymodel");
                              
   }
   
   @Test
   public void testStubs_parameterTypesTest() throws Exception {
      doTestStubs("StubGeneratorUtil_testStubs_parameterTypesTest",
                  "data/parameterTypesTest/test",
                  "data/parameterTypesTest/oracleStubs");
   }
   
   @Test 
   public void testExtractReferences_fullInheritenceTest() throws CoreException, InterruptedException {
      doExtractReferencesTest("JDTUtilTest_testGetReferenceMap_fullInheritenceTest",
                              "data/fullInheritenceTest/test",
                              "data/fullInheritenceTest/oracle/Dependencymodel.dependencymodel");                          
   }
   
   @Test
   public void testStubs_fullInheritenceTest() throws Exception {
      doTestStubs("StubGeneratorUtil_testStubs_fullInheritenceTest",
                  "data/fullInheritenceTest/test",
                  "data/fullInheritenceTest/oracleStubs");
   }
   
   @Test
   public void testExtractReferences_interfaceInheritenceTest() throws CoreException, InterruptedException {
      doExtractReferencesTest("JDTUtilTest_testGetReferenceMap_interfaceInheritenceTest", 
                              "data/interfaceInheritenceTest/test",
                              "data/interfaceInheritenceTest/oracle/Dependencymodel.dependencymodel");
   }
   
   @Test
   public void testStubs_interfaceInheritenceTest() throws Exception {
      doTestStubs("StubGeneratorUtil_testStubs_interfaceInheritenceTest",
                  "data/interfaceInheritenceTest/test",
                  "data/interfaceInheritenceTest/oracleStubs");
   }
   
   @Test
   public void testExtractReferences_genericsTest() throws CoreException, InterruptedException {
      doExtractReferencesTest("JDTUtilTest_testGetReferenceMap_genericsTest",
                              "data/genericsTest/test", 
                              "data/genericsTest/oracle/Dependencymodel.dependencymodel");                           
   }
   
   @Test
   public void testStubs_genericsTest() throws Exception {
      doTestStubs("StubGeneratorUtil_testStubs_genericsTest",
                  "data/genericsTest/test",
                  "data/genericsTest/oracleStubs");
   }
   
   @Test
   public void testExtractReferences_arrayTest() throws CoreException, InterruptedException {
      doExtractReferencesTest("JDTUtilTest_testGetReferenceMap_arrayTest",
                              "data/arrayTest/test", 
                              "data/arrayTest/oracle/Dependencymodel.dependencymodel");                           
   }
   
   @Test
   public void testStubs_arrayTest() throws Exception {
      doTestStubs("StubGeneratorUtil_testStubs_arrayTest",
                  "data/arrayTest/test",
                  "data/arrayTest/oracleStubs");
   }
   
   @Test
   public void testExtractReferences_fieldDeclarationTest() throws CoreException, InterruptedException {
      doExtractReferencesTest("JDTUtilTest_testGetReferenceMap_fieldDeclarationTest",
                              "data/fieldDeclarationTest/test", 
                              "data/fieldDeclarationTest/oracle/Dependencymodel.dependencymodel");                           
   }
   
   @Test
   public void testStubs_fieldDeclarationTest() throws Exception {
      doTestStubs("StubGeneratorUtil_testStubs_fieldDeclarationTest",
                  "data/fieldDeclarationTest/test",
                  "data/fieldDeclarationTest/oracleStubs");
   }
   
   @Test
   public void testExtractReferences_multiInterfaceInheritance() throws CoreException, InterruptedException {
      doExtractReferencesTest("JDTUtilTest_testGetReferenceMap_multiInterfaceInheritance",
                              "data/multiInterfaceInheritance/test", 
                              "data/multiInterfaceInheritance/oracle/Dependencymodel.dependencymodel");                           
   }
   
   @Test
   public void testStubs_multiInterfaceInheritance() throws Exception {
      doTestStubs("StubGeneratorUtil_multiInterfaceInheritance",
                  "data/multiInterfaceInheritance/test",
                  "data/multiInterfaceInheritance/oracleStubs");
   }
   
   @Test
   public void testExtractReferences_multileGenericArguments() throws CoreException, InterruptedException {
      doExtractReferencesTest("JDTUtilTest_testGetReferenceMap_multileGenericArguments",
                              "data/multileGenericArguments/test", 
                              "data/multileGenericArguments/oracle/Dependencymodel.dependencymodel");                           
   }
   
   @Test
   public void testStubs_multileGenericArguments() throws Exception {
      doTestStubs("StubGeneratorUtil_testStubs_multileGenericArguments",
                  "data/multileGenericArguments/test",
                  "data/multileGenericArguments/oracleStubs");
   }
   
   @Test
   public void testExtractReferences_simpleGenericMethodArgument() throws CoreException, InterruptedException {
      doExtractReferencesTest("JDTUtilTest_testGetReferenceMap_simpleGenericMethodArgument",
                              "data/simpleGenericMethodArgument/test", 
                              "data/simpleGenericMethodArgument/oracle/Dependencymodel.dependencymodel");                           
   }
   
   @Test
   public void testStubs_simpleGenericMethodArgument() throws Exception {
      doTestStubs("StubGeneratorUtil_testStubs_simpleGenericMethodArgument",
                  "data/simpleGenericMethodArgument/test",
                  "data/simpleGenericMethodArgument/oracleStubs");
   }
   
   @Test
   public void testExtractReferences_simpleGenericTest() throws CoreException, InterruptedException {
      doExtractReferencesTest("JDTUtilTest_testGetReferenceMap_simpleGenericTest",
                              "data/simpleGenericTest/test", 
                              "data/simpleGenericTest/oracle/Dependencymodel.dependencymodel");                           
   }
   
   @Test
   public void testStubs_simpleGenericTest() throws Exception {
      doTestStubs("StubGeneratorUtil_testStubs_simpleGenericTest",
                  "data/simpleGenericTest/test",
                  "data/simpleGenericTest/oracleStubs");
   }
   
   @Test
   public void testExtractReferences_simpleGenericTypeArgument() throws CoreException, InterruptedException {
      doExtractReferencesTest("JDTUtilTest_testGetReferenceMap_simpleGenericTypeArgument",
                              "data/simpleGenericTypeArgument/test", 
                              "data/simpleGenericTypeArgument/oracle/Dependencymodel.dependencymodel");                           
   }
   
   @Test
   public void testStubs_simpleGenericTypeArgument() throws Exception {
      doTestStubs("StubGeneratorUtil_testStubs_simpleGenericTypeArgument",
                  "data/simpleGenericTypeArgument/test",
                  "data/simpleGenericTypeArgument/oracleStubs");
   }
   
   @Test
   public void testExtractReferences_simpleInnerType() throws CoreException, InterruptedException {
      doExtractReferencesTest("JDTUtilTest_testGetReferenceMap_simpleInnerType",
                              "data/simpleInnerType/test", 
                              "data/simpleInnerType/oracle/Dependencymodel.dependencymodel");                           
   }
   
   @Test
   public void testStubs_simpleInnerType() throws Exception {
      doTestStubs("StubGeneratorUtil_testStubs_simpleInnerType",
                  "data/simpleInnerType/test",
                  "data/simpleInnerType/oracleStubs");
   }
 
   @Test
   public void testExtractReferences_multiParamTest() throws CoreException, InterruptedException {
      doExtractReferencesTest("JDTUtilTest_testGetReferenceMap_multiParamTest",
                              "data/multiParamTest/test", 
                              "data/multiParamTest/oracle/Dependencymodel.dependencymodel");
                                                        
   }
   
   @Test
   public void testStubs_multiParamTest() throws Exception {
      doTestStubs("StubGeneratorUtil_testStubs_multiParamTest",
                  "data/multiParamTest/test",
                  "data/multiParamTest/oracleStubs");
   }
   
   @Test
   public void testExtractReferences_sameParamTest() throws CoreException, InterruptedException {
      doExtractReferencesTest("JDTUtilTest_testGetReferenceMap_sameParamTest",
                              "data/sameParamTest/test", 
                              "data/sameParamTest/oracle/Dependencymodel.dependencymodel");
                                                        
   }

   @Test
   public void testStubs_sameParamTest() throws Exception {
      doTestStubs("StubGeneratorUtil_testStubs_sameParamTest",
                  "data/sameParamTest/test",
                  "data/sameParamTest/oracleStubs");
   }
   
   @Test
   public void testStubRegeneration_replaceMethodContent() throws Exception {
      doChangedTestStubs("StubGeneratorUtil_testStubRegeneration_replaceMethodContent",
                         "data/stubRegeneration_replaceMethodContent/test",
                         "data/stubRegeneration_replaceMethodContent/initialStubs",
                         "data/stubRegeneration_replaceMethodContent/oracleStubs");
   }
   
   @Test
   public void testStubRegeneration_keepMethodContent() throws Exception {
      doChangedTestStubs("StubGeneratorUtil_testStubRegeneration_keepMethodContent",
                         "data/stubRegeneration_keepMethodContent/test",
                         "data/stubRegeneration_keepMethodContent/initialStubs",
                         "data/stubRegeneration_keepMethodContent/oracleStubs");
   }
   
   @Test
   public void testStubRegeneration_keepAnnotationContent() throws Exception {
      doChangedTestStubs("StubGeneratorUtil_testStubRegeneration_keepAnnotationContent",
                         "data/stubRegeneration_keepAnnotationContent/test",
                         "data/stubRegeneration_keepAnnotationContent/initialStubs",
                         "data/stubRegeneration_keepAnnotationContent/oracleStubs");
   }
   
   @Test
   public void testStubRegeneration_addMethod() throws Exception {
      doChangedTestStubs("StubGeneratorUtil_testStubRegeneration_addMethod",
                         "data/stubRegeneration_addMethod/test",
                         "data/stubRegeneration_addMethod/initialStubs",
                         "data/stubRegeneration_addMethod/oracleStubs");
   }
   
   
   @Test
   public void testStubRegeneration_addField() throws Exception {
      doChangedTestStubs("StubGeneratorUtil_testStubRegeneration_addField",
                         "data/stubRegeneration_addField/test",
                         "data/stubRegeneration_addField/initialStubs",
                         "data/stubRegeneration_addField/oracleStubs");
   }
   
   @Test
   public void testStubRegeneration_removeMethod() throws Exception {
      doChangedTestStubs("StubGeneratorUtil_testStubRegeneration_removeMethod",
                         "data/stubRegeneration_removeMethod/test",
                         "data/stubRegeneration_removeMethod/initialStubs",
                         "data/stubRegeneration_removeMethod/oracleStubs");
   }
   
   @Test
   public void testStubRegeneration_removeField() throws Exception {
      doChangedTestStubs("StubGeneratorUtil_testStubRegeneration_removeField",
                         "data/stubRegeneration_removeField/test",
                         "data/stubRegeneration_removeField/initialStubs",
                         "data/stubRegeneration_removeField/oracleStubs");
   }
   
   @Test
   public void testStubRegeneration_removeMethodAnnotation() throws Exception {
      doChangedTestStubs("StubGeneratorUtil_testStubRegeneration_removeMethodAnnotation",
                         "data/stubRegeneration_removeMethodAnnotation/test",
                         "data/stubRegeneration_removeMethodAnnotation/initialStubs",
                         "data/stubRegeneration_removeMethodAnnotation/oracleStubs");
   }
   
   @Test
   public void testStubRegeneration_removeFieldAnnotation() throws Exception {
      doChangedTestStubs("StubGeneratorUtil_testStubRegeneration_removeFieldAnnotation",
                         "data/stubRegeneration_removeFieldAnnotation/test",
                         "data/stubRegeneration_removeFieldAnnotation/initialStubs",
                         "data/stubRegeneration_removeFieldAnnotation/oracleStubs");
   }
   
   @Test
   public void testStubRegeneration_keepField() throws Exception {
      doChangedTestStubs("StubGeneratorUtil_testStubRegeneration_keepField",
                         "data/stubRegeneration_keepField/test",
                         "data/stubRegeneration_keepField/initialStubs",
                         "data/stubRegeneration_keepField/oracleStubs");
   }
   
   @Test
   public void testStubRegeneration_changeField() throws Exception {
      doChangedTestStubs("StubGeneratorUtil_testStubRegeneration_changeField",
                         "data/stubRegeneration_changeField/test",
                         "data/stubRegeneration_changeField/initialStubs",
                         "data/stubRegeneration_changeField/oracleStubs");
   }
   
   @Test
   public void testStubRegeneration_keepInnerTypes() throws Exception {
      doChangedTestStubs("StubGeneratorUtil_testStubRegeneration_keepInnerTypes",
                         "data/stubRegeneration_keepInnerTypes/test",
                         "data/stubRegeneration_keepInnerTypes/initialStubs",
                         "data/stubRegeneration_keepInnerTypes/oracleStubs");
   }
   
   @Test
   public void testStubRegeneration_addInnerTypes() throws Exception {
      doChangedTestStubs("StubGeneratorUtil_testStubRegeneration_addInnerTypes",
                         "data/stubRegeneration_addInnerTypes/test",
                         "data/stubRegeneration_addInnerTypes/initialStubs",
                         "data/stubRegeneration_addInnerTypes/oracleStubs");
   }
   
   @Test
   public void testStubRegeneration_changeInnerTypes() throws Exception {
      doChangedTestStubs("StubGeneratorUtil_testStubRegeneration_changeInnerTypes",
                         "data/stubRegeneration_changeInnerTypes/test",
                         "data/stubRegeneration_changeInnerTypes/initialStubs",
                         "data/stubRegeneration_changeInnerTypes/oracleStubs");
   }
   
   protected void doTestStubs(String stubProject, 
                              String pathToTestDataInPlugin, 
                              String pathToOracleStubsFileInPlugin) throws Exception {
      // Create project and add code to generate stubs from
      IJavaProject project = TestUtilsUtil.createJavaProject(stubProject);
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, pathToTestDataInPlugin, project.getProject().getFolder("src"));
      // Generate stubs
      StubGeneratorUtil.generateStubs(project);
      // Extract oracle stubs into project
      IFolder oracleFolder = project.getProject().getFolder("oracleStubs");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, pathToOracleStubsFileInPlugin, oracleFolder);
      // Create new oracle stubs if requested
      createOracleFiles(project, pathToOracleStubsFileInPlugin);
      // Compare generated stubs with oracle stubs
      IFolder stubFolder = project.getProject().getFolder(StubGeneratorUtil.STUB_FOLDER_NAME);
      assertResources(oracleFolder.members(), stubFolder.members());
   }

   /**
    * Creates new oracle files if required.
    * @param project The current {@link IJavaProject}.
    * @param pathToOracleStubsFileInPlugin The path to the oracle files in the {@link Bundle}.
    * @throws CoreException Occurred Exception.
    */
   protected static void createOracleFiles(IJavaProject project, String pathToOracleStubsFileInPlugin) throws CoreException {
      if (oracleDirectory != null) {
         File oracleSubDirectory = new File(oracleDirectory, pathToOracleStubsFileInPlugin);
         oracleSubDirectory.mkdirs();
         assertTrue(ResourceUtil.copyIntoFileSystem(project.getProject().getFolder(StubGeneratorUtil.STUB_FOLDER_NAME), oracleSubDirectory));
         printOracleDirectory();
      }
   }
   
   /**
    * Prints {@link #oracleDirectory} to the user via {@link System#out}.
    */
   protected static void printOracleDirectory() {
      if (oracleDirectory != null) {
         final String HEADER_LINE = "Oracle Directory is:";
         final String PREFIX = "### ";
         final String SUFFIX = " ###";
         String path = oracleDirectory.toString();
         int length = Math.max(path.length(), HEADER_LINE.length());
         String borderLines = StringUtil.createLine("#", PREFIX.length() + length + SUFFIX.length());
         System.out.println(borderLines);
         System.out.println(PREFIX + HEADER_LINE + StringUtil.createLine(" ", length - HEADER_LINE.length()) + SUFFIX);
         System.out.println(PREFIX + path + StringUtil.createLine(" ", length - path.length()) + SUFFIX);
         System.out.println(borderLines);
      }
   }
   
   protected void doChangedTestStubs(String stubProject, 
                                     String pathToTestDataInPlugin, 
                                     String pathToInitialStubs,
                                     String pathToOracleStubsFileInPlugin) throws Exception {
      // Create project
      IJavaProject project = TestUtilsUtil.createJavaProject(stubProject);
      // Fill src folder
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, pathToTestDataInPlugin, project.getProject().getFolder("src"));
      // Fill stub folder
      IFolder stubFolder = project.getProject().getFolder(StubGeneratorUtil.STUB_FOLDER_NAME);
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, pathToInitialStubs, stubFolder);
      // Generate stubs
      StubGeneratorUtil.generateStubs(project);
      // Extract oracle stubs into project
      IFolder oracleFolder = project.getProject().getFolder("oracleStubs");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, pathToOracleStubsFileInPlugin, oracleFolder);
      // Create new oracle stubs if requested
      createOracleFiles(project, pathToOracleStubsFileInPlugin);
      // Compare generated stubs with oracle stubs
      assertResources(oracleFolder.members(), stubFolder.members());
   }
   

   public static void assertResources(IResource[] expected, IResource[] current) throws Exception {
      if (expected != null) {
         assertNotNull(current);
         assertEquals(expected.length, current.length);
         for (int i = 0; i < expected.length; i++) {
            assertResource(expected[i], current[i]);
         }
      }
      else {
         assertNull(current);
      }
   }
  
   public static void assertResource(IResource expected, IResource current) throws Exception {
      assertEquals(expected.getName(), current.getName());
      assertEquals(expected.getType(), current.getType());
      if (expected instanceof IFolder) {
         assertTrue(current instanceof IFolder);
         assertResources(((IFolder) expected).members(), ((IFolder) current).members());
      }
      else {
         assertFalse(current instanceof IFolder);
      }
      if (expected instanceof IFile) {
         assertTrue(current instanceof IFile);
         String expectedContent = IOUtil.readFrom(((IFile) expected).getContents());
         String currentContent = IOUtil.readFrom(((IFile) current).getContents());
         assertEquals(expectedContent, currentContent);
      }
      else {
         assertFalse(current instanceof IFile);
      }
    }

   /**
    * Method test the extracted References 
    * @param projectName {@link String}
    * @param pathToTestDataInPlugin {@link String}
    * @param expectedTypes {@link Typ}
    * @throws CoreException
    * @throws InterruptedException
    */
   protected void doExtractReferencesTest(String projectName,
                                          String pathToTestDataInPlugin,
                                          String pathToOracleFileInPlugin) throws CoreException, InterruptedException {
      // Create project with Source Folders and ASTNode to test
      IJavaProject project = TestUtilsUtil.createJavaProject(projectName, "src");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, pathToTestDataInPlugin, project.getProject().getFolder("src"));
      List<IPackageFragmentRoot> sourceFolders = JDTUtil.getSourceFolders(project);
      List<ICompilationUnit> icompUnitList = JDTUtil.listCompilationUnit(sourceFolders);
      List<AbstractType> testTypes = new LinkedList<AbstractType>();
      for (ICompilationUnit icompUnit : icompUnitList) {
         //ICompilationUnit icompunit = JDTUtil.listCompilationUnit(sourceFolders).get(0); // TODO: For all found files
         //System.out.println(icompunit.getElementName());
         ASTNode ast = JDTUtil.parse(icompUnit);
         // Compute references
         testTypes = StubGeneratorUtil.extractTypesAndMembers(ast);
         //testTypes.addAll(StubGeneratorUtil.extractTypesAndMembers(ast));
      }
      // Load oracle file
      ResourceSet rst = new ResourceSetImpl();
      Resource resource = rst.getResource(URI.createPlatformPluginURI("/" + Activator.PLUGIN_ID + "/" + pathToOracleFileInPlugin, true), true);
      assertEquals(1, resource.getContents().size());
      assertTrue(resource.getContents().get(0) instanceof DependencyModel);
      DependencyModel expectedModel = (DependencyModel) resource.getContents().get(0);
      //AbstractType[] expectedTypes = expectedModel.getTypes().toArray(new AbstractType[expectedModel.getTypes().size()]);
      List<AbstractType> expectedTypes = expectedModel.getTypes();
      // Test types
      assertAbstractTypes(expectedTypes, testTypes, new HashSet<AbstractType>());
      assertEquals("Number of types", expectedTypes.size(), testTypes.size());
   }
   
   private void assertAbstractTypes(List<? extends AbstractType> expectedTypes, List<? extends AbstractType> actualTypes, Set<AbstractType> nownAbstractTypes) {
      assertEquals("Number of types", expectedTypes.size(), actualTypes.size());
      Iterator<? extends AbstractType> expectTypIter = expectedTypes.iterator();
      Iterator<? extends AbstractType> actualTypIter = actualTypes.iterator();
      while( expectTypIter.hasNext() && actualTypIter.hasNext()){
         AbstractType expectedType = expectTypIter.next();
         AbstractType actualType = actualTypIter.next();
         assertAbstractType(expectedType, actualType, nownAbstractTypes);
      }
      assertFalse(expectTypIter.hasNext());
      assertFalse(actualTypIter.hasNext());
   }

   private void assertAbstractType(AbstractType expectedType, AbstractType actualType, Set<AbstractType> nownAbstractTypes) {
      if (nownAbstractTypes.add(actualType)) {
         if (expectedType instanceof Type) {
            assertTrue(actualType instanceof Type);
            assertType((Type) expectedType, (Type) actualType, nownAbstractTypes);
         }
         else if (expectedType instanceof GenericType) {
            assertTrue(actualType instanceof GenericType);
            assertGenericType((GenericType) expectedType, (GenericType) actualType, nownAbstractTypes);
         }
         else if (expectedType instanceof Datatype) {
            assertTrue(actualType instanceof Datatype);
            assertDatatype((Datatype) expectedType, (Datatype) actualType);
         }
         else if (expectedType instanceof WildcardType) {
            assertTrue(actualType instanceof WildcardType);
            assertWildcardType((WildcardType) expectedType, (WildcardType) actualType);
         }
         else if (expectedType instanceof ArrayType) {
            assertTrue(actualType instanceof ArrayType);
            assertArrayType((ArrayType) expectedType, (ArrayType) actualType, nownAbstractTypes);
         }
         else if (expectedType instanceof TypeVariable) {
            assertTrue(actualType instanceof TypeVariable);
            assertTypeVariables((TypeVariable) expectedType, (TypeVariable) actualType, nownAbstractTypes);
         }
         else if (expectedType == null) {
            assertNull(actualType); 
         }
         else{
           fail("Unsupported type");
         }
      }
   }
   
   private void assertArrayType(ArrayType expectedType, ArrayType actualType, Set<AbstractType> nownAbstractTypes) {
      internalAbstractType(expectedType, actualType);
      assertAbstractType(expectedType.getBaseType(), actualType.getBaseType(), nownAbstractTypes);
   }

   private void assertWildcardType(WildcardType expectedType, WildcardType actualType) {
      internalAbstractType(expectedType, actualType);
   }

   private void assertDatatype(Datatype expectedType, Datatype actualType) {
      internalAbstractType(expectedType, actualType);
   }
   private void assertTypeVariables(TypeVariable expectedType, TypeVariable actualType, Set<AbstractType> nownAbstractTypes) {
      internalAbstractType(expectedType, actualType);
      assertAbstractType(expectedType.getType(), actualType.getType(), nownAbstractTypes);
   }

   private void assertGenericType(GenericType expectedType, GenericType actualType, Set<AbstractType> nownAbstractTypes) {
      internalAbstractType(expectedType, actualType);
      assertAbstractTypes(expectedType.getTypeArguments(), actualType.getTypeArguments(), nownAbstractTypes);
      assertAbstractType(expectedType.getBaseType(), actualType.getBaseType(), nownAbstractTypes);
   }

   private void assertType(Type expectedType, Type actualType, Set<AbstractType> nownAbstractTypes) {
      internalAbstractType(expectedType, actualType);
      assertEquals(expectedType.isAbstract(), actualType.isAbstract());
      assertEquals(expectedType.isFinal(), actualType.isFinal());
      assertEquals(expectedType.isStatic(), actualType.isStatic());
      assertEquals(expectedType.getKind(), actualType.getKind());
      assertEquals(expectedType.getPackage(), actualType.getPackage());
      assertEquals(expectedType.getSimpleName(), actualType.getSimpleName());
      assertEquals(expectedType.getVisibility(), actualType.getVisibility());
      assertAbstractTypes(expectedType.getExtends(), actualType.getExtends(), nownAbstractTypes);
      assertAbstractTypes(expectedType.getImplements(), actualType.getImplements(), nownAbstractTypes);
      assertAbstractTypes(expectedType.getInnerTypes(), actualType.getInnerTypes(), nownAbstractTypes);
      assertMethods(expectedType.getMethods(), actualType.getMethods(), nownAbstractTypes);
      assertFields(expectedType.getFields(), actualType.getFields(), nownAbstractTypes);
      assertTypeVariables(expectedType.getTypeVariables(), actualType.getTypeVariables(), nownAbstractTypes);
   }

   private void internalAbstractType(AbstractType expectedType, AbstractType actualType) {
      assertEquals(expectedType.isSource(), actualType.isSource());
      assertEquals(expectedType.getName(), actualType.getName());
   }

   /**
    * Compares expected {@link List} of {@link String} with {@link List} of {@link Method}
    * @param expected {@link List} of {@link String} 
    * @param actual {@link List} of {@link Method}
    */
   protected void assertMethods(List<Method> expected, List<Method> actual, Set<AbstractType> nownAbstractTypes) {
      assertEquals("Number of methods", expected.size(), actual.size());
      Iterator<Method> expectTypIter = expected.iterator();
      Iterator<Method> actualTypIter = actual.iterator();
      while( expectTypIter.hasNext() && actualTypIter.hasNext()){
         Method expectedMethod = expectTypIter.next();
         Method actualMethod = actualTypIter.next();
         assertMethod(expectedMethod, actualMethod, nownAbstractTypes);
      }
      assertFalse(expectTypIter.hasNext());
      assertFalse(actualTypIter.hasNext());
   }

   private void assertMethod(Method expectedType, Method actualType, Set<AbstractType> nownAbstractTypes) {
      assertEquals(expectedType.isAbstract(), actualType.isAbstract());
      assertEquals(expectedType.isFinal(), actualType.isFinal());
      assertEquals(expectedType.isStatic(), actualType.isStatic());
      assertEquals(expectedType.getName(), actualType.getName());
      assertEquals(expectedType.getVisibility(), actualType.getVisibility());
      assertAbstractTypes(expectedType.getParameterTypes(), actualType.getParameterTypes(), nownAbstractTypes);
      assertAbstractTypes(expectedType.getThrows(), actualType.getThrows(), nownAbstractTypes);
      assertAbstractType(expectedType.getReturnType(), actualType.getReturnType(), nownAbstractTypes);
      assertTypeVariables(expectedType.getTypeVariables(), actualType.getTypeVariables(), nownAbstractTypes);
   }

   /**
    * Compares List of {@link String} with {@link List} of {@link Field}
    * @param expected {@link List} of {@link String} 
    * @param actual {@link List} of {@link Field}
    */
   protected void assertFields(List<Field> expected, List<Field> actual, Set<AbstractType> nownAbstractTypes) {
      assertEquals("Number of fields", expected.size(), actual.size());
      Iterator<Field> expectTypIter = expected.iterator();
      Iterator<Field> actualTypIter = actual.iterator();
      while( expectTypIter.hasNext() && actualTypIter.hasNext()){
         Field expectedField = expectTypIter.next();
         Field actualField = actualTypIter.next();
         assertField(expectedField, actualField, nownAbstractTypes);
      }
      assertFalse(expectTypIter.hasNext());
      assertFalse(actualTypIter.hasNext());
   }

   private void assertField(Field expected, Field actual, Set<AbstractType> nownAbstractTypes) {
      assertEquals(expected.isFinal(), actual.isFinal());
      assertEquals(expected.isStatic(), actual.isStatic());
      assertEquals(expected.getConstantValue(), actual.getConstantValue());
      assertEquals(expected.getName(), actual.getName());
      assertEquals(expected.getVisibility(), actual.getVisibility());
      assertAbstractType(expected.getType(), actual.getType(), nownAbstractTypes);
   }

   private void assertTypeVariables(List<TypeVariable> expected, List<TypeVariable> actual, Set<AbstractType> nownAbstractTypes) {
      assertEquals("Number of fields", expected.size(), actual.size());
      Iterator<TypeVariable> expectTypIter = expected.iterator();
      Iterator<TypeVariable> actualTypIter = actual.iterator();
      while( expectTypIter.hasNext() && actualTypIter.hasNext()){
         TypeVariable expectedVar = expectTypIter.next();
         TypeVariable actualVar = actualTypIter.next();
         assertTypeVariable(expectedVar, actualVar, nownAbstractTypes);
      }
      assertFalse(expectTypIter.hasNext());
      assertFalse(actualTypIter.hasNext());
   }

   private void assertTypeVariable(TypeVariable expected, TypeVariable actual, Set<AbstractType> nownAbstractTypes) {
      assertEquals(expected.getName(), actual.getName());
      assertAbstractType(expected.getType(), actual.getType(), nownAbstractTypes);
   }
   
  
}