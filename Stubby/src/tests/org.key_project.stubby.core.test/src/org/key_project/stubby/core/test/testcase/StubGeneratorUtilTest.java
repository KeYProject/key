package org.key_project.stubby.core.test.testcase;

import java.io.File;
import java.io.IOException;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;

import junit.framework.TestCase;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.ResourceSet;
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl;
import org.eclipse.jdt.core.IJavaProject;
import org.junit.Test;
import org.key_project.stubby.core.test.Activator;
import org.key_project.stubby.core.util.StubGeneratorUtil;
import org.key_project.stubby.core.util.StubGeneratorUtil.IgnoredType;
import org.key_project.stubby.model.dependencymodel.DependencyModel;
import org.key_project.stubby.model.dependencymodel.Field;
import org.key_project.stubby.model.dependencymodel.Method;
import org.key_project.stubby.model.dependencymodel.Type;
import org.key_project.stubby.model.dependencymodel.TypeUsage;
import org.key_project.stubby.model.dependencymodel.TypeVariable;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.StringUtil;
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
    * are verified with the Stubby application. If everything is fine a new test
    * method can be added to this class and the first test execution can be
    * used to generate the required oracle file. Existing oracle files should
    * only be replaced if the functionality of Stubby
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
   public void testExtractReferences_javaLangUser() throws Exception{
      doDependencyModelTest("JDTUtilTest_testExtractReferences_javaLangUser", 
                            "data/javaLangUser/test",
                            "data/javaLangUser/oracle/Dependencymodel.dependencymodel");
   }

   @Test
   public void testExtractReferences_typeSetByDeclaringMethod() throws Exception{
      doDependencyModelTest("JDTUtilTest_testExtractReferences_typeSetByDeclaringMethod", 
                            "data/typeSetByDeclaringMethod/test",
                            "data/typeSetByDeclaringMethod/oracle/Dependencymodel.dependencymodel");
   }

   @Test
   public void testExtractReferences_missingTypeParameters() throws Exception{
      doDependencyModelTest("JDTUtilTest_testExtractReferences_missingTypeParameters", 
                            "data/missingTypeParameters/test",
                            "data/missingTypeParameters/oracle/Dependencymodel.dependencymodel");
   }

   @Test
   public void testExtractReferences_genericTypeUsedInDeclaration() throws Exception{
      doDependencyModelTest("JDTUtilTest_testExtractReferences_genericTypeUsedInDeclaration", 
                            "data/genericTypeUsedInDeclaration/test",
                            "data/genericTypeUsedInDeclaration/oracle/Dependencymodel.dependencymodel");
   }

   @Test
   public void testExtractReferences_starImports() throws Exception{
      doDependencyModelTest("JDTUtilTest_testExtractReferences_starImports", 
                            "data/starImports/test",
                            "data/starImports/oracle/Dependencymodel.dependencymodel");
   }

   @Test
   public void testExtractReferences_ImmutableMap() throws Exception{
      doDependencyModelTest("JDTUtilTest_testExtractReferences_ImmutableMap", 
                            "data/ImmutableMap/test",
                            "data/ImmutableMap/oracle/Dependencymodel.dependencymodel");
   }

   @Test
   public void testExtractReferences_LRUCache() throws Exception{
      doDependencyModelTest("JDTUtilTest_testExtractReferences_LRUCache", 
                            "data/LRUCache/test",
                            "data/LRUCache/oracle/Dependencymodel.dependencymodel");
   }

   @Test
   public void testExtractReferences_wildcardTest() throws Exception{
      doDependencyModelTest("JDTUtilTest_testExtractReferences_wildcardTest", 
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
   public void testExtractReferences_importTest() throws Exception{
      doDependencyModelTest("JDTUtilTest_testExtractReferences_importTest", 
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
   public void testExtractReferences_innerTypeTest() throws Exception{
      doDependencyModelTest("JDTUtilTest_testExtractReferences_innerTypeTest", 
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
   public void testExtractReferences_methodCallTest() throws Exception{
      doDependencyModelTest("JDTUtilTest_testGetReferenceMap_methodCallTest", 
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
   public void testExtractReferences_superMethodCallTest() throws Exception {
      doDependencyModelTest("JDTUtilTest_testGetReferenceMap_superMethodCallTest",
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
   public void testExtractReferences_implicitSuperMethodCallTest() throws Exception {
      doDependencyModelTest("JDTUtilTest_testGetReferenceMap_implicitSuper",
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
   public void testExtractReferences_fieldCallTest() throws Exception {
      doDependencyModelTest("JDTUtilTes_testGetReferenceMap_fieldCallTest",
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
   public void testExtractReferences_superFieldCallTest() throws Exception {
      doDependencyModelTest("JDTUtilTest_testGetReferenceMap_superFieldCallTest", 
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
      doDependencyModelTest("JDTUtilTest_testGetReferenceMap_implicitSuperFieldCallTest", 
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
      doDependencyModelTest("JDTUtilTest_testGetReferenceMap_implicitFieldCallTest", 
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
      doDependencyModelTest("JDTUtilTest_testGetReferenceMap_nestedFieldCallTest",
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
   public void testExtractReferences_constructorCallTest() throws Exception {
      doDependencyModelTest("JDTUtilTest_testGetReferenceMap_constructorCallTest", 
                            "data/constructorCallTest/test",
                            "data/constructorCallTest/oracle/Dependencymodel.dependencymodel");
   }
   
   @Test
   public void testStubs_starImports() throws Exception {
      doTestStubs("StubGeneratorUtil_testStubs_starImports",
                  "data/starImports/test",
                  "data/starImports/oracleStubs");
   }
   
   @Test
   public void testStubs_constructorCallTest() throws Exception {
      doTestStubs("StubGeneratorUtil_testStubs_constructorCallTest",
                  "data/constructorCallTest/test",
                  "data/constructorCallTest/oracleStubs");
   }
   
   @Test 
   public void testExtractReferences_superConstructorCallTest() throws Exception {
      doDependencyModelTest("JDTUtilTest_testGetReferenceMap_superConstructorCallTest", 
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
      doDependencyModelTest("JDTUtilTest_testGetReferenceMap_implicitSuperConstructorCallTest", 
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
   public void testExtractReferences_innerThisTest() throws Exception {
      doDependencyModelTest("JDTUtilTest_testGetReferenceMap_innerThisTest", 
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
      doDependencyModelTest("JDTUtilTest_testGetReferenceMap_fieldOnMethodCallTeset", 
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
   public void testExtractReferences_nestedFieldOnMethodCallTest() throws Exception {
      doDependencyModelTest("JDTUtilTest_testGetReferenceMap_nestedFieldOnMethodCallTeset",
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
   public void testExtractReferences_parameterTypesTest() throws Exception {
      doDependencyModelTest("JDTUtilTest_testGetReferenceMap_parameterTypesTest",
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
   public void testStubs_GenericParamTest() throws Exception {
      doTestStubs("StubGeneratorUtil_testStubs_GenericParamTest",
                  "data/GenericParamTest/test",
                  "data/GenericParamTest/oracleStubs");
   }
   
   @Test 
   public void testExtractReferences_fullInheritenceTest() throws Exception {
      doDependencyModelTest("JDTUtilTest_testGetReferenceMap_fullInheritenceTest",
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
   public void testExtractReferences_interfaceInheritenceTest() throws Exception {
      doDependencyModelTest("JDTUtilTest_testGetReferenceMap_interfaceInheritenceTest", 
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
   public void testExtractReferences_genericsTest() throws Exception {
      doDependencyModelTest("JDTUtilTest_testGetReferenceMap_genericsTest",
                            "data/genericsTest/test", 
                            "data/genericsTest/oracle/Dependencymodel.dependencymodel");                           
   }
   
   @Test
   public void testExtractReferences_genericParamTest() throws Exception {
      doDependencyModelTest("JDTUtilTest_testExtractReferences_genericParamTest",
                            "data/GenericParamTest/test", 
                            "data/GenericParamTest/oracle/Dependencymodel.dependencymodel");                           
   }
   
   @Test
   public void testStubs_genericsTest() throws Exception {
      doTestStubs("StubGeneratorUtil_testStubs_genericsTest",
                  "data/genericsTest/test",
                  "data/genericsTest/oracleStubs");
   }
   
   @Test
   public void testStubs_javaLangUser() throws Exception {
      doTestStubs("StubGeneratorUtil_testStubs_javaLangUser",
                  "data/javaLangUser/test",
                  "data/javaLangUser/oracleStubs");
   }
   
   @Test
   public void testExtractReferences_arrayTest() throws Exception {
      doDependencyModelTest("JDTUtilTest_testGetReferenceMap_arrayTest",
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
   public void testExtractReferences_fieldDeclarationTest() throws Exception {
      doDependencyModelTest("JDTUtilTest_testGetReferenceMap_fieldDeclarationTest",
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
   public void testExtractReferences_multiInterfaceInheritance() throws Exception {
      doDependencyModelTest("JDTUtilTest_testGetReferenceMap_multiInterfaceInheritance",
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
   public void testExtractReferences_multileGenericArguments() throws Exception {
      doDependencyModelTest("JDTUtilTest_testGetReferenceMap_multileGenericArguments",
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
   public void testExtractReferences_simpleGenericMethodArgument() throws Exception {
      doDependencyModelTest("JDTUtilTest_testGetReferenceMap_simpleGenericMethodArgument",
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
   public void testExtractReferences_simpleGenericTest() throws Exception {
      doDependencyModelTest("JDTUtilTest_testGetReferenceMap_simpleGenericTest",
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
   public void testExtractReferences_simpleGenericTypeArgument() throws Exception {
      doDependencyModelTest("JDTUtilTest_testGetReferenceMap_simpleGenericTypeArgument",
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
   public void testExtractReferences_simpleInnerType() throws Exception {
      doDependencyModelTest("JDTUtilTest_testGetReferenceMap_simpleInnerType",
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
   public void testExtractReferences_multiParamTest() throws Exception {
      doDependencyModelTest("JDTUtilTest_testGetReferenceMap_multiParamTest",
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
   public void testExtractReferences_sameParamTest() throws Exception {
      doDependencyModelTest("JDTUtilTest_testGetReferenceMap_sameParamTest",
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
   public void testStubRegeneration_removeInnerTypes() throws Exception {
      doChangedTestStubs("StubGeneratorUtil_testStubRegeneration_replaceMethodContent",
                         "data/stubRegeneration_removeInnerTypes/test",
                         "data/stubRegeneration_removeInnerTypes/initialStubs",
                         "data/stubRegeneration_removeInnerTypes/oracleStubs");
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
   public void testStubRegeneration_addConstructor() throws Exception {
      doChangedTestStubs("StubGeneratorUtil_stubRegeneration_addConstructor",
                         "data/stubRegeneration_addConstructor/test",
                         "data/stubRegeneration_addConstructor/initialStubs",
                         "data/stubRegeneration_addConstructor/oracleStubs");
   }
   
   @Test
   public void testStubRegeneration_addConstructorAgain() throws Exception {
      doChangedTestStubs("StubGeneratorUtil_stubRegeneration_addConstructorAgain",
                         "data/stubRegeneration_addConstructorAgain/test",
                         "data/stubRegeneration_addConstructorAgain/initialStubs",
                         "data/stubRegeneration_addConstructorAgain/oracleStubs");
   }
   
   @Test
   public void testStubRegeneration_removeAndKeepConstructor() throws Exception {
      doChangedTestStubs("StubGeneratorUtil_stubRegeneration_removeAndKeepConstructor",
                         "data/stubRegeneration_removeAndKeepConstructor/test",
                         "data/stubRegeneration_removeAndKeepConstructor/initialStubs",
                         "data/stubRegeneration_removeAndKeepConstructor/oracleStubs");
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

   /**
    * Tests the created {@link DependencyModel}.
    * @param projectName The name of the {@link IJavaProject} to perform test in.
    * @param pathToSourceFilesInPlugin The path to the source files in the {@link Bundle}.
    * @param pathToOracleFileInPlugin The path to the oracle file in the {@link Bundle}.
    * @throws Exception Occurred Exception.
    */
   protected void doDependencyModelTest(String projectName,
                                        String pathToSourceFilesInPlugin,
                                        String pathToOracleFileInPlugin) throws Exception {
      // Create project with Source Folders and ASTNode to test
      IJavaProject project = TestUtilsUtil.createJavaProject(projectName, "src");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, pathToSourceFilesInPlugin, project.getProject().getFolder("src"));
      // Create dependency model
      DependencyModel dependencyModel = StubGeneratorUtil.createDependencyModel(project, null);
      // Create new oracle files if needed
      createOracleFiles(dependencyModel, pathToOracleFileInPlugin);
      // Load oracle file
      ResourceSet rst = new ResourceSetImpl();
      Resource resource = rst.getResource(URI.createPlatformPluginURI("/" + Activator.PLUGIN_ID + "/" + pathToOracleFileInPlugin, true), true);
      assertEquals(1, resource.getContents().size());
      assertTrue(resource.getContents().get(0) instanceof DependencyModel);
      DependencyModel expectedModel = (DependencyModel) resource.getContents().get(0);
      // Test model
      assertDependenyModel(expectedModel, dependencyModel);
   }   
   
   /**
    * Creates a new oracle file in the temporary directory.
    * @param dependencyModel The current {@link DependencyModel}.
    * @param pathToOracleFileInPlugin The path to the oracle file in the {@link Bundle}.
    * @throws IOException Occurred Exception
    */
   protected static void createOracleFiles(DependencyModel dependencyModel, String pathToOracleFileInPlugin) throws IOException {
      if (oracleDirectory != null) {
         File oracleFile = new File(oracleDirectory, pathToOracleFileInPlugin);
         oracleFile.getParentFile().mkdirs();
         ResourceSet rst = new ResourceSetImpl();
         Resource resource = rst.createResource(URI.createFileURI(oracleFile.getAbsolutePath()));
         resource.getContents().add(dependencyModel);
         resource.save(Collections.EMPTY_MAP);
         printOracleDirectory();
      }
   }

   /**
    * Performs a stub generation test.
    * @param projectName The name of the {@link IJavaProject} to perform test in.
    * @param pathToSourceFilesInPlugin The path to the test data in the {@link Bundle}.
    * @param pathToOracleStubsFileInPlugin The path to the oracle files in the {@link Bundle}.
    * @throws Exception Occurred Exception.
    */
   protected void doTestStubs(String projectName, 
                              String pathToSourceFilesInPlugin, 
                              String pathToOracleStubsFileInPlugin) throws Exception {
      // Create project and add code to generate stubs from
      IJavaProject project = TestUtilsUtil.createJavaProject(projectName);
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, pathToSourceFilesInPlugin, project.getProject().getFolder("src"));
      // Generate stubs
      List<IgnoredType> ignoredTyps = StubGeneratorUtil.generateStubs(project, StubGeneratorUtil.DEFAULT_STUB_FOLDER_PATH, null);
      assertNotNull(ignoredTyps);
      assertEquals(0, ignoredTyps.size());
      // Extract oracle stubs into project
      IFolder oracleFolder = project.getProject().getFolder("oracleStubs");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, pathToOracleStubsFileInPlugin, oracleFolder);
      // Create new oracle stubs if requested
      createOracleFiles(project, pathToOracleStubsFileInPlugin);
      // Compare generated stubs with oracle stubs
      IFolder stubFolder = project.getProject().getFolder(StubGeneratorUtil.DEFAULT_STUB_FOLDER_PATH);
      TestUtilsUtil.assertResources(oracleFolder.members(), stubFolder.members());
   }

   /**
    * Performs a stub generation test with existing stubs.
    * @param projectName The name of the {@link IJavaProject} to perform test in.
    * @param pathToSourceFilesInPlugin The path to the test data in the {@link Bundle}.
    * @param pathToInitialStubs The path to the existing stubs in the {@link Bundle}.
    * @param pathToOracleStubsFileInPlugin The path to the oracle files in the {@link Bundle}.
    * @throws Exception Occurred Exception.
    */
   protected void doChangedTestStubs(String projectName, 
                                     String pathToSourceFilesInPlugin, 
                                     String pathToInitialStubs,
                                     String pathToOracleStubsFileInPlugin) throws Exception {
      // Create project
      IJavaProject project = TestUtilsUtil.createJavaProject(projectName);
      // Fill src folder
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, pathToSourceFilesInPlugin, project.getProject().getFolder("src"));
      // Fill stub folder
      IFolder stubFolder = project.getProject().getFolder(StubGeneratorUtil.DEFAULT_STUB_FOLDER_PATH);
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, pathToInitialStubs, stubFolder);
      // Generate stubs
      List<IgnoredType> ignoredTyps = StubGeneratorUtil.generateStubs(project, StubGeneratorUtil.DEFAULT_STUB_FOLDER_PATH, null);
      assertNotNull(ignoredTyps);
      assertEquals(0, ignoredTyps.size());
      // Extract oracle stubs into project
      IFolder oracleFolder = project.getProject().getFolder("oracleStubs");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, pathToOracleStubsFileInPlugin, oracleFolder);
      // Create new oracle stubs if requested
      createOracleFiles(project, pathToOracleStubsFileInPlugin);
      // Compare generated stubs with oracle stubs
      TestUtilsUtil.assertResources(oracleFolder.members(), stubFolder.members());
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
         assertTrue(ResourceUtil.copyIntoFileSystem(project.getProject().getFolder(StubGeneratorUtil.DEFAULT_STUB_FOLDER_PATH), oracleSubDirectory));
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
   
   /**
    * Ensures the same content of the given {@link DependencyModel}s.
    * @param expected The expected {@link DependencyModel}.
    * @param current The current {@link DependencyModel}.
    * @throws Exception Occurred Exception.
    */
   protected void assertDependenyModel(DependencyModel expected, DependencyModel current) {
      if (expected != null) {
         assertNotNull(current);
         assertTypes(expected.getTypes(), current.getTypes());
      }
      else {
         assertNull(current);
      }
   }
   
   /**
    * Ensures the same content of the given {@link Type}s.
    * @param expected The expected {@link Type}s.
    * @param current The current {@link Type}s.
    * @throws Exception Occurred Exception.
    */
   protected void assertTypes(List<Type> expected, 
                              List<Type> current) {
      assertEquals("Number of types", expected.size(), current.size());
      Iterator<Type> expectTypIter = expected.iterator();
      Iterator<Type> actualTypIter = current.iterator();
      while( expectTypIter.hasNext() && actualTypIter.hasNext()){
         Type expectedType = expectTypIter.next();
         Type actualType = actualTypIter.next();
         assertType(expectedType, actualType);
      }
      assertFalse(expectTypIter.hasNext());
      assertFalse(actualTypIter.hasNext());
   }

   /**
    * Ensures the same content of the given {@link Type}s.
    * @param expected The expected {@link Type}.
    * @param current The current {@link Type}.
    * @throws Exception Occurred Exception.
    */
   protected void assertType(Type expected, 
                             Type current) {
      assertEquals(expected.isAbstract(), current.isAbstract());
      assertEquals(expected.isFinal(), current.isFinal());
      assertEquals(expected.isSource(), current.isSource());
      assertEquals(expected.isStatic(), current.isStatic());
      assertTypeUsages(expected.getExtends(), current.getExtends());
      assertFields(expected.getFields(), current.getFields());
      assertTypeUsages(expected.getImplements(), current.getImplements());
      assertTypes(expected.getInnerTypes(), current.getInnerTypes());
      assertEquals(expected.getKind(), current.getKind());
      assertMethods(expected.getMethods(), current.getMethods());
      assertEquals(expected.getName(), current.getName());
      assertEquals(expected.getPackage(), current.getPackage());
      assertEquals(expected.getSimpleName(), current.getSimpleName());
      assertTypeVariables(expected.getTypeVariables(), current.getTypeVariables());
      assertEquals(expected.getVisibility(), current.getVisibility());
   }
   
   /**
    * Ensures the same content of the given {@link TypeUsage}s.
    * @param expected The expected {@link TypeUsage}s.
    * @param current The current {@link TypeUsage}s.
    * @throws Exception Occurred Exception.
    */
   protected void assertTypeUsages(List<TypeUsage> expected, 
                                   List<TypeUsage> current) {
      assertEquals("Number of type usages", expected.size(), current.size());
      Iterator<TypeUsage> expectTypIter = expected.iterator();
      Iterator<TypeUsage> actualTypIter = current.iterator();
      while( expectTypIter.hasNext() && actualTypIter.hasNext()){
         TypeUsage expectedType = expectTypIter.next();
         TypeUsage actualType = actualTypIter.next();
         assertTypeUsage(expectedType, actualType);
      }
      assertFalse(expectTypIter.hasNext());
      assertFalse(actualTypIter.hasNext());
   }
   
   /**
    * Ensures the same content of the given {@link TypeUsage}s.
    * @param expected The expected {@link TypeUsage}.
    * @param current The current {@link TypeUsage}.
    * @throws Exception Occurred Exception.
    */
   protected void assertTypeUsage(TypeUsage expected,
                                  TypeUsage current) {
      assertEquals(expected.getGenericFreeType(), current.getGenericFreeType());
      assertEquals(expected.getType(), current.getType());
   }

   /**
    * Ensures the same content of the given {@link Method}s.
    * @param expected The expected {@link Method}s.
    * @param current The current {@link Method}s.
    * @throws Exception Occurred Exception.
    */
   protected void assertMethods(List<Method> expected, 
                                List<Method> current) {
      assertEquals("Number of methods", expected.size(), current.size());
      Iterator<Method> expectTypIter = expected.iterator();
      Iterator<Method> actualTypIter = current.iterator();
      while( expectTypIter.hasNext() && actualTypIter.hasNext()){
         Method expectedMethod = expectTypIter.next();
         Method actualMethod = actualTypIter.next();
         assertMethod(expectedMethod, actualMethod);
      }
      assertFalse(expectTypIter.hasNext());
      assertFalse(actualTypIter.hasNext());
   }

   /**
    * Ensures the same content of the given {@link Method}s.
    * @param expected The expected {@link Method}.
    * @param current The current {@link Method}.
    * @throws Exception Occurred Exception.
    */
   protected void assertMethod(Method expected, 
                               Method current) {
      assertEquals(expected.isAbstract(), current.isAbstract());
      assertEquals(expected.isConstructor(), current.isConstructor());
      assertEquals(expected.isFinal(), current.isFinal());
      assertEquals(expected.isStatic(), current.isStatic());
      assertEquals(expected.getName(), current.getName());
      assertTypeUsages(expected.getParameterTypes(), current.getParameterTypes());
      assertTypeUsage(expected.getReturnType(), current.getReturnType());
      assertTypeUsages(expected.getThrows(), current.getThrows());
      assertTypeVariables(expected.getTypeVariables(), current.getTypeVariables());
      assertEquals(expected.getVisibility(), current.getVisibility());
   }

   /**
    * Ensures the same content of the given {@link Field}s.
    * @param expected The expected {@link Field}s.
    * @param current The current {@link Field}s.
    * @throws Exception Occurred Exception.
    */
   protected void assertFields(List<Field> expected, 
                               List<Field> current) {
      assertEquals("Number of fields", expected.size(), current.size());
      Iterator<Field> expectTypIter = expected.iterator();
      Iterator<Field> actualTypIter = current.iterator();
      while( expectTypIter.hasNext() && actualTypIter.hasNext()){
         Field expectedField = expectTypIter.next();
         Field actualField = actualTypIter.next();
         assertField(expectedField, actualField);
      }
      assertFalse(expectTypIter.hasNext());
      assertFalse(actualTypIter.hasNext());
   }

   /**
    * Ensures the same content of the given {@link Field}s.
    * @param expected The expected {@link Field}.
    * @param current The current {@link Field}.
    * @throws Exception Occurred Exception.
    */
   protected void assertField(Field expected, 
                              Field current) {
      assertEquals(expected.isFinal(), current.isFinal());
      assertEquals(expected.isStatic(), current.isStatic());
      assertEquals(expected.getConstantValue(), current.getConstantValue());
      assertEquals(expected.getName(), current.getName());
      assertTypeUsage(expected.getType(), current.getType());
      assertEquals(expected.getVisibility(), current.getVisibility());
   }

   /**
    * Ensures the same content of the given {@link TypeVariable}s.
    * @param expected The expected {@link TypeVariable}s.
    * @param current The current {@link TypeVariable}s.
    * @throws Exception Occurred Exception.
    */
   protected void assertTypeVariables(List<TypeVariable> expected, 
                                      List<TypeVariable> current) {
      assertEquals("Number of fields", expected.size(), current.size());
      Iterator<TypeVariable> expectTypIter = expected.iterator();
      Iterator<TypeVariable> actualTypIter = current.iterator();
      while( expectTypIter.hasNext() && actualTypIter.hasNext()){
         TypeVariable expectedVar = expectTypIter.next();
         TypeVariable actualVar = actualTypIter.next();
         assertTypeVariable(expectedVar, actualVar);
      }
      assertFalse(expectTypIter.hasNext());
      assertFalse(actualTypIter.hasNext());
   }

   /**
    * Ensures the same content of the given {@link TypeVariable}s.
    * @param expected The expected {@link TypeVariable}.
    * @param current The current {@link TypeVariable}.
    * @throws Exception Occurred Exception.
    */
   protected void assertTypeVariable(TypeVariable expected, 
                                     TypeVariable current) {
      assertEquals(expected.getName(), current.getName());
      assertTypeUsage(expected.getType(), current.getType());
   }
}