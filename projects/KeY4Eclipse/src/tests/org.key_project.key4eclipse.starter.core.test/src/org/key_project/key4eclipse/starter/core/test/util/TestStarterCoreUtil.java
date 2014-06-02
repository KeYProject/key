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

package org.key_project.key4eclipse.starter.core.test.util;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;

import java.io.File;
import java.util.List;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.Assert;
import org.eclipse.jdt.core.IMethod;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.util.jdt.JDTUtil;

import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.symbolic_execution.po.ProgramMethodPO;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

/**
 * Provides static methods that makes testing easier.
 * @author Martin Hentschel
 */
public final class TestStarterCoreUtil {
   /**
    * Forbid instances.
    */
   private TestStarterCoreUtil() {
   }

   /**
    * Instantiates a proof in KeY for the given {@link IMethod} with a default
    * generated contract.
    * @param method The {@link IMethod} to proof.
    * @return The instantiated {@link Proof}.
    * @throws Exception Occurred Exception.
    */
   public static Proof instantiateProofWithGeneratedContract(final IMethod method, boolean addUninterpretedPredicate, boolean startAutoMode) throws Exception {
      // make sure that the method has a resource
      Assert.isNotNull(method.getResource(), "Method \"" + method + "\" is not part of a workspace resource.");
      // Make sure that the location is contained in a Java project
      IProject project = method.getResource().getProject();
      Assert.isTrue(JDTUtil.isJavaProject(project), " The project \"" + project + "\" is no Java project.");
      // Get KeY project settings
      final File bootClassPath = KeYResourceProperties.getKeYBootClassPathLocation(project);
      final List<File> classPaths = KeYResourceProperties.getKeYClassPathEntries(project);
      // Get local file for the eclipse resource
      final File location = KeYUtil.getSourceLocation(project);
      Assert.isNotNull(location, "The resource \"" + method.getResource() + "\" is not local.");
      // Load environment
      KeYEnvironment<CustomConsoleUserInterface> environment = KeYEnvironment.load(location, classPaths, bootClassPath);
      IProgramMethod pm = KeYUtil.getProgramMethod(method, environment.getJavaInfo());
      ProofOblInput input = new ProgramMethodPO(environment.getInitConfig(), pm.getFullName(), pm, null, addUninterpretedPredicate, false);
      Proof proof = environment.createProof(input);
      assertNotNull(proof);
      assertFalse(proof.closed());
      if (startAutoMode) {
         environment.getUi().startAndWaitForAutoMode(proof);
      }
      return proof;
      
      
//      // Open main window to avoid repaint bugs
//      KeYUtil.openMainWindow();
//      // Load location and open proof management dialog
//      IRunnableWithResult<Proof> run = new AbstractRunnableWithResult<Proof>() {
//          @Override
//          public void run() {
//              try {
//                  // Make sure that main window is available.
//                  Assert.isTrue(MainWindow.hasInstance(), "KeY main window is not available.");
//                  MainWindow main = MainWindow.getInstance();
//                  Assert.isNotNull(main, "KeY main window is not available.");
//                  // Load location
//                  KeYEnvironment<?> environment = KeYEnvironment.loadInMainWindow(location, classPaths, bootClassPath, true);
//                  InitConfig initConfig = environment.getInitConfig();
//                  // Get method to proof in KeY
//                  IProgramMethod pm = KeYUtil.getProgramMethod(method, initConfig.getServices().getJavaInfo());
//                  Assert.isNotNull(pm, "Can't find method \"" + method + "\" in KeY.");
//                  // Create TextualJMLSpecCase
//                  ImmutableList<String> mods = ImmutableSLList.nil();
//                  mods = mods.append("public");
//                  TextualJMLSpecCase textualSpecCase = new TextualJMLSpecCase(mods, Behavior.NORMAL_BEHAVIOR);
//                  if (!pm.isStatic()) {
//                     textualSpecCase.addRequires(new PositionedString("this.<inv>")); // Assume own invariants
//                  }
//                  // Create contract
//                  JMLSpecFactory factory = new JMLSpecFactory(environment.getServices());
//                  ImmutableSet<Contract> contracts = factory.createJMLOperationContracts(pm, textualSpecCase);
//                  Contract contract = contracts.iterator().next();
//                  // Make sure that a contract is defined
//                  if (contract == null) {
//                      throw new CoreException(LogUtil.getLogger().createErrorStatus("Unable to find a contract to prove."));
//                  }
//                  // Instantiate proof
//                  ProofOblInput input = new FunctionalOperationContractPO(initConfig, (FunctionalOperationContract)contract);
//                  ProblemInitializer init = main.getUserInterface().createProblemInitializer();
//                  Proof proof = init.startProver(initConfig, input, 0);
//                  setResult(proof);
//              }
//              catch (Exception e) {
//                  setException(e);
//              }
//          }
//      };
//      SwingUtil.invokeAndWait(run);
//      if (run.getException() != null) {
//          throw run.getException();
//      }
//      return run.getResult();
   }
}