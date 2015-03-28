// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.control;

import java.io.File;
import java.util.List;
import java.util.Properties;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader.ReplayResult;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;

/**
 * Instances of this class are used to collect and access all
 * relevant information for verification with KeY.
 * @author Martin Hentschel
 */
public class KeYEnvironment<U extends UserInterfaceControl> {
   /**
    * The {@link UserInterfaceControl} in which the {@link Proof} is loaded.
    */
   private final U ui;
   
   /**
    * The loaded project.
    */
   private final InitConfig initConfig;
   
   /**
    * An optional {@link Proof} which was loaded by the specified proof file. 
    */
   private final Proof loadedProof;
   
   /**
    * Indicates that this {@link KeYEnvironment} is disposed.
    */
   private boolean disposed;

   /**
    * The {@link ReplayResult} if available.
    */
   private final ReplayResult replayResult;

   /**
    * Constructor
    * @param ui The {@link UserInterfaceControl} in which the {@link Proof} is loaded.
    * @param initConfig The loaded project.
    */
   public KeYEnvironment(U ui, InitConfig initConfig) {
      this(ui, initConfig, null, null);
   }

   /**
    * Constructor
    * @param ui The {@link UserInterfaceControl} in which the {@link Proof} is loaded.
    * @param initConfig The loaded project.
    */
   public KeYEnvironment(U ui, InitConfig initConfig, Proof loadedProof, ReplayResult replayResult) {
      this.ui = ui;
      this.initConfig = initConfig;
      this.loadedProof = loadedProof;
      this.replayResult = replayResult;
   }

   /**
    * Returns the {@link UserInterfaceControl} in which the {@link Proof} is loaded.
    * @return The {@link UserInterfaceControl} in which the {@link Proof} is loaded.
    */
   public U getUi() {
      return ui;
   }
   
   /**
    * Returns the {@link ProofControl} of {@link #getUi()}.
    * @return The {@link ProofControl} of {@link #getUi()}.
    */
   public ProofControl getProofControl() {
      return ui != null ? ui.getProofControl() : null;
   }

   /**
    * Returns the loaded project.
    * @return The loaded project.
    */
   public InitConfig getInitConfig() {
      return initConfig;
   }

   /**
    * Returns the {@link Services} of {@link #getInitConfig()}.
    * @return The {@link Services} of {@link #getInitConfig()}.
    */
   public Services getServices() {
      return initConfig.getServices();
   }

   /**
    * Returns the used {@link JavaInfo}.
    * @return The used {@link JavaInfo}.
    */
   public JavaInfo getJavaInfo() {
      return getServices().getJavaInfo();
   }

   /**
    * Returns the used {@link SpecificationRepository}.
    * @return The used {@link SpecificationRepository}.
    */
   public SpecificationRepository getSpecificationRepository() {
      return getServices().getSpecificationRepository();
   }

   public Profile getProfile() {
      return getInitConfig().getProfile();
   }
   
   /**
    * Returns the loaded {@link Proof} if a proof file was loaded.
    * @return The loaded {@link Proof} if available and {@code null} otherwise.
    */
   public Proof getLoadedProof() {
      return loadedProof;
   }

   /**
    * Returns the {@link ReplayResult} if available.
    * @return The {@link ReplayResult} or {@code null} if not available.
    */
   public ReplayResult getReplayResult() {
      return replayResult;
   }

   /**
    * Creates a new {@link Proof} with help of the {@link UserInterfaceControl}.
    * @param input The {@link ProofOblInput} to instantiate {@link Proof} from.
    * @return The instantiated {@link Proof}.
    * @throws ProofInputException Occurred Exception.
    */
   public Proof createProof(ProofOblInput input) throws ProofInputException {
      return ui.createProof(getInitConfig(), input);
   }
   
   /**
    * Loads the given location and returns all required references as {@link KeYEnvironment}.
    * The {@link MainWindow} is not involved in the whole process.
    * @param location The location to load.
    * @param classPaths The class path entries to use.
    * @param bootClassPath The boot class path to use.
    * @return The {@link KeYEnvironment} which contains all references to the loaded location.
    * @throws ProblemLoaderException Occurred Exception
    */
   public static KeYEnvironment<DefaultUserInterfaceControl> load(File location,
                                                          List<File> classPaths,
                                                          File bootClassPath) throws ProblemLoaderException {
      return load(null, location, classPaths, bootClassPath, false);
   }
   
   /**
    * Loads the given location and returns all required references as {@link KeYEnvironment}.
    * The {@link MainWindow} is not involved in the whole process.
    * @param location The location to load.
    * @param classPaths The class path entries to use.
    * @param bootClassPath The boot class path to use.
    * @param ruleCompletionHandler An optional {@link RuleCompletionHandler}.
    * @return The {@link KeYEnvironment} which contains all references to the loaded location.
    * @throws ProblemLoaderException Occurred Exception
    */
   public static KeYEnvironment<DefaultUserInterfaceControl> load(File location,
                                                          List<File> classPaths,
                                                          File bootClassPath,
                                                          RuleCompletionHandler ruleCompletionHandler) throws ProblemLoaderException {
      return load(null, location, classPaths, bootClassPath, null, ruleCompletionHandler, false);
   }
   
   /**
    * Loads the given location and returns all required references as {@link KeYEnvironment}.
    * The {@link MainWindow} is not involved in the whole process.
    * @param profile The {@link Profile} to use.
    * @param location The location to load.
    * @param classPaths The class path entries to use.
    * @param bootClassPath The boot class path to use.
    * @param forceNewProfileOfNewProofs {@code} true {@link #profileOfNewProofs} will be used as {@link Profile} of new proofs, {@code false} {@link Profile} specified by problem file will be used for new proofs.
    * @return The {@link KeYEnvironment} which contains all references to the loaded location.
    * @throws ProblemLoaderException Occurred Exception
    */
   public static KeYEnvironment<DefaultUserInterfaceControl> load(Profile profile,
                                                          File location,
                                                          List<File> classPaths,
                                                          File bootClassPath,
                                                          boolean forceNewProfileOfNewProofs) throws ProblemLoaderException {
      return load(profile, location, classPaths, bootClassPath, null, null, forceNewProfileOfNewProofs);
   }
   
   /**
    * Loads the given location and returns all required references as {@link KeYEnvironment}.
    * The {@link MainWindow} is not involved in the whole process.
    * @param profile The {@link Profile} to use.
    * @param location The location to load.
    * @param classPaths The class path entries to use.
    * @param bootClassPath The boot class path to use.
    * @param poPropertiesToForce Some optional PO {@link Properties} to force.
    * @param ruleCompletionHandler An optional {@link RuleCompletionHandler}.
    * @param forceNewProfileOfNewProofs {@code} true {@link #profileOfNewProofs} will be used as {@link Profile} of new proofs, {@code false} {@link Profile} specified by problem file will be used for new proofs.
    * @return The {@link KeYEnvironment} which contains all references to the loaded location.
    * @throws ProblemLoaderException Occurred Exception
    */
   public static KeYEnvironment<DefaultUserInterfaceControl> load(Profile profile,
                                                          File location,
                                                          List<File> classPaths,
                                                          File bootClassPath,
                                                          Properties poPropertiesToForce,
                                                          RuleCompletionHandler ruleCompletionHandler,
                                                          boolean forceNewProfileOfNewProofs) throws ProblemLoaderException {
      DefaultUserInterfaceControl ui = new DefaultUserInterfaceControl(ruleCompletionHandler);
      AbstractProblemLoader loader = ui.load(profile, location, classPaths, bootClassPath, poPropertiesToForce, forceNewProfileOfNewProofs); 
      InitConfig initConfig = loader.getInitConfig();
      return new KeYEnvironment<DefaultUserInterfaceControl>(ui, initConfig, loader.getProof(), loader.getResult());
   }

   /**
    * Disposes this {@link KeYEnvironment}.
    */
   public void dispose() {
      if (loadedProof != null && !loadedProof.isDisposed()) {
         loadedProof.dispose();
      }
      disposed = true;
   }
   
   /**
    * Checks if this {@link KeYEnvironment} is disposed meaning that
    * {@link #dispose()} was already executed at least once.
    * @return {@code true} disposed, {@code false} not disposed and still functionable.
    */
   public boolean isDisposed() {
      return disposed;
   }
}