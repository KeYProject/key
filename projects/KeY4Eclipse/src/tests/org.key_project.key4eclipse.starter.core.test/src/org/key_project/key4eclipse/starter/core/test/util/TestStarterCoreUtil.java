package org.key_project.key4eclipse.starter.core.test.util;

import java.io.File;
import java.util.List;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IMethod;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.key4eclipse.starter.core.util.LogUtil;
import org.key_project.util.java.SwingUtil;
import org.key_project.util.java.thread.AbstractRunnableWithResult;
import org.key_project.util.java.thread.IRunnableWithResult;
import org.key_project.util.jdt.JDTUtil;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.FunctionalOperationContractPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.jml.pretranslation.Behavior;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase;
import de.uka.ilkd.key.speclang.jml.translation.JMLSpecFactory;

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
   public static Proof instantiateProofWithGeneratedContract(final IMethod method) throws Exception {
      // make sure that the method has a resource
      Assert.isNotNull(method.getResource(), "Method \"" + method + "\" is not part of a workspace resource.");
      // Make sure that the location is contained in a Java project
      IProject project = method.getResource().getProject();
      Assert.isTrue(JDTUtil.isJavaProject(project), " The project \"" + project + "\" is no Java project.");
      // Get source paths from class path
      List<File> sourcePaths = JDTUtil.getSourceLocations(project);
      Assert.isTrue(1 == sourcePaths.size(), "Multiple source paths are not supported.");
      // Get KeY project settings
      final File bootClassPath = KeYResourceProperties.getKeYBootClassPathLocation(project);
      final List<File> classPaths = KeYResourceProperties.getKeYClassPathEntries(project);
      // Get local file for the eclipse resource
      final File location = sourcePaths.get(0);
      Assert.isNotNull(location, "The resource \"" + method.getResource() + "\" is not local.");
      // Open main window to avoid repaint bugs
      KeYUtil.openMainWindow();
      // Load location and open proof management dialog
      IRunnableWithResult<Proof> run = new AbstractRunnableWithResult<Proof>() {
          @Override
          public void run() {
              try {
                  // Make sure that main window is available.
                  Assert.isTrue(MainWindow.hasInstance(), "KeY main window is not available.");
                  MainWindow main = MainWindow.getInstance();
                  Assert.isNotNull(main, "KeY main window is not available.");
                  // Load location
                  InitConfig initConfig = KeYUtil.internalLoad(location, classPaths, bootClassPath, true);
                  // Get method to proof in KeY
                  ProgramMethod pm = KeYUtil.getProgramMethod(method, initConfig.getServices().getJavaInfo());
                  Assert.isNotNull(pm, "Can't find method \"" + method + "\" in KeY.");
                  // Get contract to proof
                  Services services = initConfig.getServices();
                  // Create TextualJMLSpecCase
                  ImmutableList<String> mods = ImmutableSLList.nil();
                  mods = mods.append("public");
                  TextualJMLSpecCase textualSpecCase = new TextualJMLSpecCase(mods, Behavior.NORMAL_BEHAVIOR);
                  if (!pm.isStatic()) {
                     textualSpecCase.addRequires(new PositionedString("this.<inv>")); // Assume own invariants
                  }
                  // Create contract
                  JMLSpecFactory factory = new JMLSpecFactory(services);
                  ImmutableSet<Contract> contracts = factory.createJMLOperationContracts(pm, textualSpecCase);
                  Contract contract = contracts.iterator().next();
                  // Make sure that a contract is defined
                  if (contract == null) {
                      throw new CoreException(LogUtil.getLogger().createErrorStatus("Unable to find a contract to prove."));
                  }
                  // Instantiate proof
                  ProofOblInput input = new FunctionalOperationContractPO(initConfig, (FunctionalOperationContract)contract);
                  ProblemInitializer init = main.getUserInterface().createProblemInitializer();
                  Proof proof = init.startProver(initConfig, input, 0);
                  setResult(proof);
              }
              catch (Exception e) {
                  setException(e);
              }
          }
      };
      SwingUtil.invokeAndWait(run);
      if (run.getException() != null) {
          throw run.getException();
      }
      return run.getResult();
   }
}
