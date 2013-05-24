// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.symbolic_execution.util;

import java.io.File;
import java.util.List;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.DefaultProblemLoader;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;
import de.uka.ilkd.key.ui.UserInterface;

/**
 * Instances of this class are used to collect and access all
 * relevant information for verification with KeY.
 * @author Martin Hentschel
 */
public class KeYEnvironment<U extends UserInterface> {
   /**
    * The {@link UserInterface} in which the {@link Proof} is loaded.
    */
   private U ui;
   
   /**
    * The loaded project.
    */
   private InitConfig initConfig;
   
   /**
    * An optional {@link Proof} which was loaded by the specified proof file. 
    */
   private Proof loadedProof;

   /**
    * Constructor
    * @param ui The {@link UserInterface} in which the {@link Proof} is loaded.
    * @param initConfig The loaded project.
    */
   public KeYEnvironment(U ui, InitConfig initConfig) {
      this(ui, initConfig, null);
   }

   /**
    * Constructor
    * @param ui The {@link UserInterface} in which the {@link Proof} is loaded.
    * @param initConfig The loaded project.
    */
   public KeYEnvironment(U ui, InitConfig initConfig, Proof loadedProof) {
      this.ui = ui;
      this.initConfig = initConfig;
      this.loadedProof = loadedProof;
   }

   /**
    * Returns the {@link UserInterface} in which the {@link Proof} is loaded.
    * @return The {@link UserInterface} in which the {@link Proof} is loaded.
    */
   public U getUi() {
      return ui;
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
    * Returns the used {@link KeYMediator}.
    * @return The used {@link KeYMediator}.
    */
   public KeYMediator getMediator() {
      return ui.getMediator();
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
      return getMediator().getProfile();
   }
   
   /**
    * Returns the loaded {@link Proof} if a proof file was loaded.
    * @return The loaded {@link Proof} if available and {@code null} otherwise.
    */
   public Proof getLoadedProof() {
      return loadedProof;
   }

   /**
    * Creates a new {@link Proof} with help of the {@link UserInterface}.
    * @param input The {@link ProofOblInput} to instantiate {@link Proof} from.
    * @return The instantiated {@link Proof}.
    * @throws ProofInputException Occurred Exception.
    */
   public Proof createProof(ProofOblInput input) throws ProofInputException {
      return ui.createProof(getInitConfig(), input);
   }
   
   /**
    * Loads the given location and returns all required references as {@link KeYEnvironment}
    * with KeY's {@link MainWindow}.
    * @param location The location to load.
    * @param classPaths The class path entries to use.
    * @param bootClassPath The boot class path to use.
    * @param makeMainWindowVisible Make KeY's {@link MainWindow} visible if it is not already visible?
    * @return The {@link KeYEnvironment} which contains all references to the loaded location.
    * @throws ProblemLoaderException Occurred Exception
    */
   public static KeYEnvironment<UserInterface> loadInMainWindow(File location,
                                                                List<File> classPaths,
                                                                File bootClassPath,
                                                                boolean makeMainWindowVisible) throws ProblemLoaderException {
      MainWindow main = MainWindow.getInstance();
      if (makeMainWindowVisible && !main.isVisible()) {
          main.setVisible(true);
      }
      DefaultProblemLoader loader = main.getUserInterface().load(location, classPaths, bootClassPath);
      InitConfig initConfig = loader.getInitConfig();
      return new KeYEnvironment<UserInterface>(main.getUserInterface(), initConfig, loader.getProof());
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
   public static KeYEnvironment<CustomConsoleUserInterface> load(File location,
                                                                 List<File> classPaths,
                                                                 File bootClassPath) throws ProblemLoaderException {
      CustomConsoleUserInterface ui = new CustomConsoleUserInterface(false);
      DefaultProblemLoader loader = ui.load(location, classPaths, bootClassPath); 
      InitConfig initConfig = loader.getInitConfig();
      return new KeYEnvironment<CustomConsoleUserInterface>(ui, initConfig, loader.getProof());
   }

   /**
    * Disposes this {@link KeYEnvironment}.
    */
   public void dispose() {
      if (loadedProof != null) {
         loadedProof.dispose();
      }
   }
}