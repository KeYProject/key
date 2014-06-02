/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package de.hentschel.visualdbc.key.ui.test.testCase;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.junit.Test;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.test.util.TestUtilsUtil;

import de.hentschel.visualdbc.key.ui.test.Activator;
import de.hentschel.visualdbc.key.ui.util.ProofReferenceModelCreator;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof_references.ProofReferenceUtil;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionStrategy;
import de.uka.ilkd.key.symbolic_execution.util.IFilter;
import de.uka.ilkd.key.symbolic_execution.util.JavaUtil;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;

/**
 * Tests {@link ProofReferenceModelCreator}.
 * @author Martin Hentschel
 */
public class ProofReferenceModelCreatorTest extends AbstractProofReferenceModelCreatorTest {
   /**
    * Tests "ConstructorTest".
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testConstructorTest() throws Exception {
      doTest("ProofReferenceModelCreatorTest_testConstructorTest", 
             "data/ConstructorTest/test", 
             "ConstructorTest.java", 
             "ConstructorTest", 
             "ConstructorTest::ConstructorTest",
             "data/ConstructorTest/oracle/Initial.xml",
             false,
             "data/ConstructorTest/oracle/Final.xml");
   }
   
   /**
    * Tests "InnerAndAnonymousTypeTest".
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testInnerAndAnonymousTypeTest() throws Exception {
      doTest("ProofReferenceModelCreatorTest_testInnerAndAnonymousTypeTest", 
             "data/InnerAndAnonymousTypeTest/test", 
             "Main.java", 
             "Main", 
             "Main::main",
             "data/InnerAndAnonymousTypeTest/oracle/Initial.xml",
             false,
             "data/InnerAndAnonymousTypeTest/oracle/Final.xml");
   }

   /**
    * Tests "ModelFieldTest".
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testModelFieldTest() throws Exception {
      doTest("ProofReferenceModelCreatorTest_testModelFieldTest", 
             "data/ModelFieldTest/test", 
             "ModelFieldTest.java", 
             "test.ModelFieldTest", 
             "test.ModelFieldTest::doubleX",
             "data/ModelFieldTest/oracle/Initial.xml",
             false,
             "data/ModelFieldTest/oracle/Final.xml");
   }

   /**
    * Tests "AttributeAndEnumLiteralTest".
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testAttributeAndEnumLiteralTest() throws Exception {
      doTest("ProofReferenceModelCreatorTest_testAttributeAndEnumLiteralTest", 
             "data/AttributeAndEnumLiteralTest/test", 
             "Main.java", 
             "Main", 
             "Main::main",
             "data/AttributeAndEnumLiteralTest/oracle/Initial.xml",
             false,
             "data/AttributeAndEnumLiteralTest/oracle/Final.xml");
   }

   /**
    * Tests "MethodTest".
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testMethodTest() throws Exception {
      doTest("ProofReferenceModelCreatorTest_testMethodTest", 
             "data/MethodTest/test", 
             "Main.java", 
             "Main", 
             "Main::main",
             "data/MethodTest/oracle/Initial.xml",
             false,
             "data/MethodTest/oracle/Final.xml");
   }

   /**
    * Tests "OperationContractTest".
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testOperationContractTest() throws Exception {
      doTest("ProofReferenceModelCreatorTest_testOperationContractTest", 
             "data/OperationContractTest/test", 
             "Main.java", 
             "Main", 
             "Main::main",
             "data/OperationContractTest/oracle/Initial.xml",
             true,
             "data/OperationContractTest/oracle/Final.xml");
   }

   /**
    * Tests "AccessibleTest".
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testAccessibleTest() throws Exception {
      doTest("ProofReferenceModelCreatorTest_testAccessibleTest", 
             "data/AccessibleTest/test", 
             "AccessibleTest.java", 
             "test.B", 
             "java.lang.Object::<inv>",
             "data/AccessibleTest/oracle/Initial.xml",
             false,
             "data/AccessibleTest/oracle/Final.xml");
   }
   
   /**
    * Executes the test steps of all test cases provided by this class.
    * @param projectName The name of the project to create.
    * @param pathInBundle The path to source files in the bundle to extract to the created project.
    * @param javaFileInProject The path to the java file to open in the created project.
    * @param containerTypeName The name of the type to prove.
    * @param targetName The name of the proof obligation.
    * @param initialOracleFileInBundle The path to the initial oracle file in the bundle.
    * @param useContracts {@code true} use contracts, {@code false} inline methods.
    * @param finalOracleFileInBundle The path to the final oracle file in the bundle.
    * @throws Exception Occurred Exception.
    */
   protected void doTest(String projectName, 
                         String pathInBundle,
                         String javaFileInProject,
                         String containerTypeName,
                         final String targetName,
                         String initialOracleFileInBundle,
                         boolean useContracts,
                         String finalOracleFileInBundle) throws Exception {
      KeYEnvironment<?> environment = null;
      Proof proof = null;
      try {
         // Create test project
         IProject project = TestUtilsUtil.createProject(projectName);
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, pathInBundle, project);
         IFile javaFile = project.getFile(new Path(javaFileInProject));
         assertTrue(javaFile.exists());
         // Create Proof
         environment = KeYEnvironment.load(ResourceUtil.getLocation(javaFile), null, null);
         // Search type
         KeYJavaType containerKJT = environment.getJavaInfo().getTypeByClassName(containerTypeName);
         assertNotNull(containerKJT);
         // Search observer function
         ImmutableSet<IObserverFunction> targets = environment.getSpecificationRepository().getContractTargets(containerKJT);
         IObserverFunction target = JavaUtil.search(targets, new IFilter<IObserverFunction>() {
            @Override
            public boolean select(IObserverFunction element) {
               return targetName.equals(element.toString());
            }
         });
         assertNotNull(target);
         // Find first contract.
         ImmutableSet<Contract> contracts = environment.getSpecificationRepository().getContracts(containerKJT, target);
         assertFalse(contracts.isEmpty());
         Contract contract = contracts.iterator().next();
         // Start proof
         proof = environment.createProof(contract.createProofObl(environment.getInitConfig(), contract));
         assertNotNull(proof);
         // Compare initial model
         ProofReferenceModelCreator creator = new ProofReferenceModelCreator(proof);
         creator.updateModel(ProofReferenceUtil.computeProofReferences(proof), new NullProgressMonitor());
         compareWithOracle(oracleDirectory, creator.getModel(), Activator.PLUGIN_ID, initialOracleFileInBundle);
         // Start auto mode
         StrategyProperties sp = SymbolicExecutionStrategy.getSymbolicExecutionStrategyProperties(true, useContracts, false, false, false);
         proof.getSettings().getStrategySettings().setActiveStrategyProperties(sp);
         environment.getUi().startAndWaitForAutoMode(proof);
         // Compare final model
         creator.updateModel(ProofReferenceUtil.computeProofReferences(proof), new NullProgressMonitor());
         compareWithOracle(oracleDirectory, creator.getModel(), Activator.PLUGIN_ID, finalOracleFileInBundle);
      }
      finally {
         // Dispose proof and environment
         if (proof != null) {
            proof.dispose();
         }
         if (environment != null) {
            environment.dispose();
         }
      }
   }
}