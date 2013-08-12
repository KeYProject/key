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

import java.lang.reflect.InvocationTargetException;
import java.util.Map;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.dialogs.IMessageProvider;
import org.eclipse.ui.IWorkbench;
import org.key_project.key4eclipse.util.KeYExampleUtil;

import de.uka.ilkd.key.gui.configuration.ChoiceSettings;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
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
         throw new InvocationTargetException(e, e.getMessage());
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
      KeYEnvironment<CustomConsoleUserInterface> env = KeYEnvironment.load(KeYExampleUtil.getExampleProof(), null, null);
      env.dispose();
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected ChoiceSettings getChoiceSettings() {
      return ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Map<String, String> getDefaults() {
      return getDefaultTacletOptions();
   }
   
   /**
    * Returns the default taclet options.
    * @return The default taclet options.
    */
   public static Map<String, String> getDefaultTacletOptions() {
      return SymbolicExecutionUtil.getDefaultTacletOptions();
   }
}