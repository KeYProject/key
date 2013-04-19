/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
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

package org.key_project.key4eclipse.common.ui.preference.page;

import java.io.File;
import java.lang.reflect.InvocationTargetException;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.dialogs.IMessageProvider;
import org.eclipse.ui.IWorkbench;
import org.key_project.key4eclipse.util.KeYExampleUtil;

import de.uka.ilkd.key.gui.configuration.ChoiceSettings;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.proof.ProblemLoaderException;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

/**
 * Preference page to edit the taclet options.
 * @author Martin Hentschel
 */
public class TacletOptionsPreferencePage extends AbstractChoicePreferencePage {
   /**
    * {@inheritDoc}
    */
   @Override
   public void init(IWorkbench workbench) {
      super.init(workbench);
      setMessage("Changes will become effective when the next problem is loaded.", IMessageProvider.INFORMATION);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean isChoiceSettingsLoadingRequired() {
      return !SymbolicExecutionUtil.isChoiceSettingInitialised();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void loadChoiceSettings(IProgressMonitor monitor) throws InvocationTargetException, InterruptedException {
      try {
         monitor.beginTask("Computing Taclet Options", IProgressMonitor.UNKNOWN);
         loadChoiceSettings();
      }
      catch (Exception e) {
         throw new InvocationTargetException(e);
      }
      finally {
         monitor.done();
      }
   }
   
   /**
    * Loads the proof specified by {@link #getExampleProof()} to make sure
    * that {@link ChoiceSettings} are loaded.
    * @throws ProblemLoaderException
    */
   public static void loadChoiceSettings() throws ProblemLoaderException {
      KeYEnvironment<CustomConsoleUserInterface> env = KeYEnvironment.load(getExampleProof(), null, null);
      if (env.getLoadedProof() != null) {
         env.getLoadedProof().dispose();
      }
   }
   
   /**
    * Returns a *.key with a fast and simple proof.
    * @return A *.key with a fast and simple proof.
    */
   public static File getExampleProof() {
      String exampleDir = KeYExampleUtil.getLocalExampleDirectory();
      return new File(exampleDir, "list" + File.separator + "ArrayList_add.key");
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected ChoiceSettings getChoiceSettings() {
      return ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
   }
}