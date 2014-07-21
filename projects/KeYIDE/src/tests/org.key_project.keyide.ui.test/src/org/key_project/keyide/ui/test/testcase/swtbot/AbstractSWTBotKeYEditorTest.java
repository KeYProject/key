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

package org.key_project.keyide.ui.test.testcase.swtbot;

import org.eclipse.core.resources.IFolder;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.dialogs.MessageDialogWithToggle;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEditor;
import org.eclipse.swtbot.swt.finder.utils.SWTBotPreferences;
import org.eclipse.ui.IEditorPart;
import org.key_project.key4eclipse.common.ui.util.StarterPreferenceUtil;
import org.key_project.key4eclipse.common.ui.util.StarterUtil;
import org.key_project.keyide.ui.editor.KeYEditor;
import org.key_project.keyide.ui.starter.KeYIDEProofStarter;
import org.key_project.keyide.ui.test.Activator;
import org.key_project.keyide.ui.util.KeYIDEPreferences;
import org.key_project.keyide.ui.util.KeYIDEUtil;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.thread.AbstractRunnableWithException;
import org.key_project.util.java.thread.IRunnableWithException;
import org.key_project.util.test.testcase.AbstractSetupTestCase;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomUserInterface;

/**
 * Provides the basic functionality to test the {@link KeYEditor}.
 * @author Martin Hentschel
 */
public abstract class AbstractSWTBotKeYEditorTest extends AbstractSetupTestCase {
   /**
    * Opens a {@link Proof} in a {@link KeYEditor} and executes the given {@link IKeYEditorTestSteps}. 
    * @param projectName The project name to use.
    * @param pathToSourceFilesInBundle The path to the plug-in to the source files to extract into the created project.
    * @param contractName The name of the contract to prove.
    * @param timeoutFactor Increase the timeout by this factor.
    * @param startAutoMode Start the auto mode before the {@link KeYEditor} will be opened?
    * @param steps The {@link IKeYEditorTestSteps} to execute.
    * @throws Exception Occurred Exception.
    */
   protected void doEditorTest(String projectName,
                               String pathToSourceFilesInBundle,
                               String contractName,
                               long timeoutFactor,
                               boolean startAutoMode,
                               IKeYEditorTestSteps steps) throws Exception {
      // Store original SWTBot timeout and increase it
      long originalTimeout = SWTBotPreferences.TIMEOUT;
      SWTBotPreferences.TIMEOUT = originalTimeout * timeoutFactor;
      try {
         doEditorTest(projectName, pathToSourceFilesInBundle, contractName, startAutoMode, steps);
      }
      finally {
         // Restore original timeout
         SWTBotPreferences.TIMEOUT = originalTimeout;
      }
   }
   
   /**
    * Opens a {@link Proof} in a {@link KeYEditor} and executes the given {@link IKeYEditorTestSteps}. 
    * @param projectName The project name to use.
    * @param pathToSourceFilesInBundle The path to the plug-in to the source files to extract into the created project.
    * @param contractName The name of the contract to prove.
    * @param startAutoMode Start the auto mode before the {@link KeYEditor} will be opened?
    * @param steps The {@link IKeYEditorTestSteps} to execute.
    * @throws Exception Occurred Exception.
    */
   protected void doEditorTest(String projectName,
                               String pathToSourceFilesInBundle,
                               String contractName,
                               boolean startAutoMode,
                               IKeYEditorTestSteps steps) throws Exception {
      // Define required settings
      boolean originalDoNotAsk = StarterPreferenceUtil.isDontAskForProofStarter();
      String originalProofStarter = StarterPreferenceUtil.getSelectedProofStarterID();
      String originalSwitch = KeYIDEPreferences.getSwitchToKeyPerspective();
      StarterPreferenceUtil.setDontAskForProofStarter(true);
      StarterPreferenceUtil.setSelectedProofStarterID(KeYIDEProofStarter.STARTER_ID);
      KeYIDEPreferences.setSwitchToKeyPerspective(MessageDialogWithToggle.NEVER);
      // Close welcome view if available
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      TestUtilsUtil.closeWelcomeView(bot);
      // Create test project
      IJavaProject project = TestUtilsUtil.createJavaProject(projectName);
      IFolder src = project.getProject().getFolder("src");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, pathToSourceFilesInBundle, src);
      KeYEnvironment<CustomUserInterface> environment = null;
      Proof proof = null;
      SWTBotEditor editor = null;
      try {
         environment = KeYEnvironment.load(ResourceUtil.getLocation(src), null, null);
         Contract contract = environment.getSpecificationRepository().getContractByName(contractName);
         proof = environment.createProof(contract.createProofObl(environment.getInitConfig(), contract));
         if (startAutoMode) {
            environment.getUi().startAndWaitForAutoMode(proof);
         }
         openProof(bot, environment, proof);
         editor = bot.activeEditor();
         IEditorPart editorPart = editor.getReference().getEditor(true); 
         assertTrue(editorPart instanceof KeYEditor);
         steps.test(project, environment, proof, bot, editor, (KeYEditor)editorPart);
      }
      finally {
         StarterPreferenceUtil.setDontAskForProofStarter(originalDoNotAsk);
         StarterPreferenceUtil.setSelectedProofStarterID(originalProofStarter);
         KeYIDEPreferences.setSwitchToKeyPerspective(originalSwitch);
         bot.closeAllEditors();
         if (editor != null) {
            editor.close();
         }
         if (proof != null && !proof.isDisposed()) {
            proof.dispose();
         }
         if (environment != null) {
            environment.dispose();
         }
      }
   }
   
   /**
    * Executes the test steps of {@link AbstractSWTBotKeYEditorTest#doEditorTest(String, String, String, boolean, IKeYEditorTestSteps)}.
    * @author Martin Hentschel
    */
   protected static interface IKeYEditorTestSteps {
      /**
       * Executes the test steps.
       * @param project The {@link IJavaProject} which contains the source code.
       * @param environment The {@link KeYEnvironment} which contains the {@link Proof}.
       * @param proof The {@link Proof} shown in the {@link KeYEditor}.
       * @param bot The used {@link SWTWorkbenchBot}.
       * @param editor The used {@link SWTBotEditor} of the {@link KeYEditor}.
       * @param keyEditor The opened {@link KeYEditor}.
       * @throws Exception Occurred Exception.
       */
      public void test(IJavaProject project, 
                       KeYEnvironment<CustomUserInterface> environment, 
                       Proof proof, 
                       SWTWorkbenchBot bot,
                       SWTBotEditor editor,
                       KeYEditor keyEditor) throws Exception;
   }
   
   /**
    * Opens the given {@link Proof} via {@link StarterUtil#openProofStarter(org.eclipse.swt.widgets.Shell, Proof, KeYEnvironment, org.eclipse.jdt.core.IMethod, boolean, boolean, boolean, boolean)}.
    * @param bot The {@link SWTWorkbenchBot} to use.
    * @param environment The {@link KeYEnvironment} to use.
    * @param proof The {@link Proof} to open.
    * @throws Exception Occurred Exception.
    */
   protected void openProof(final SWTWorkbenchBot bot, 
                            final KeYEnvironment<CustomUserInterface> environment, 
                            final Proof proof) throws Exception {
      IRunnableWithException run = new AbstractRunnableWithException() {
         @Override
         public void run() {
            try {
               StarterUtil.openProofStarter(bot.activeShell().widget, proof, environment, null, true, true, true, true);
            }
            catch (Exception e) {
               setException(e);
            }
         }
      };
      Display.getDefault().syncExec(run);
      if (run.getException() != null) {
         throw run.getException();
      }
   }
   
   /**
    * Apply a {@link Taclet} manual.
    * @param mediator The {@link KeYMediator} to use.
    * @param sequent The {@link Sequent}.
    * @param inAntecedent In Antecedent?
    * @param index The index of the {@link SequentFormula}.
    * @param pit The {@link PosInTerm}.
    * @param tacletName The name of the {@link Taclet} to apply.
    */
   protected void applyTaclet(KeYMediator mediator, Sequent sequent, boolean inAntecedent, int index, PosInTerm pit, final String tacletName) {
      PosInOccurrence pio = new PosInOccurrence((inAntecedent ? sequent.antecedent() : sequent.succedent()).get(index), pit, inAntecedent);
      PosInSequent pis = PosInSequent.createCfmaPos(pio);
      ImmutableList<TacletApp> rules = KeYIDEUtil.findTaclets(mediator, pis);
      TacletApp tacletApp = CollectionUtil.search(rules, new IFilter<TacletApp>() {
         @Override
         public boolean select(TacletApp element) {
            return tacletName.equals(element.rule().name().toString());
         }
      });
      assertNotNull(tacletApp);
      mediator.selectedTaclet(tacletApp, pis);
   }
}