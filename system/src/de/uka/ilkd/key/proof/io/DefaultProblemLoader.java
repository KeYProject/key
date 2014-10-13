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

package de.uka.ilkd.key.proof.io;

import java.io.BufferedWriter;
import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.lang.reflect.Method;
import java.util.List;
import java.util.Properties;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.configuration.ProofIndependentSettings;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.parser.KeYLexer;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.init.FunctionalOperationContractPO;
import de.uka.ilkd.key.proof.init.IPersistablePO;
import de.uka.ilkd.key.proof.init.IPersistablePO.LoadedPOContainer;
import de.uka.ilkd.key.proof.init.InfFlowPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.KeYUserProblemFile;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.SLEnvInput;
import de.uka.ilkd.key.ui.UserInterface;
import de.uka.ilkd.key.util.ExceptionHandlerException;

/**
 * <p>
 * This class provides the functionality to load something it KeY.
 * The loading process is done in the current {@link Thread} and
 * no user interaction is required.
 * </p>
 * <p>
 * The basic usage of this class is to instantiate a new {@link DefaultProblemLoader}
 * instance with should load the file configured by the constructor's arguments.
 * The next step is to call {@link #load()} which does the loading process and
 * tries to instantiate a proof and to apply rules again if possible. The result
 * of the loading process is available via the getter methods.
 * </p>
 * @author Martin Hentschel
 */
public class DefaultProblemLoader {
   /**
    * The file or folder to load.
    */
   private final File file;

   /**
    * The optional class path entries to use.
    */
   private final List<File> classPath;

   /**
    * An optional boot class path.
    */
   private final File bootClassPath;

   /**
    * The {@link KeYMediator} to use.
    */
   private final KeYMediator mediator;

   /**
    * The {@link Profile} to use for new {@link Proof}s.
    */
   private final Profile profileOfNewProofs;
   
   /**
    * {@code true} to call {@link UserInterface#selectProofObligation(InitConfig)}
    * if no {@link Proof} is defined by the loaded proof or 
    * {@code false} otherwise which still allows to work with the loaded {@link InitConfig}.
    */
   private final boolean askUiToSelectAProofObligationIfNotDefinedByLoadedFile;
   
   /**
    * Some optional additional {@link Properties} for the PO.
    */
   private final Properties poPropertiesToForce;

   /**
    * The instantiated {@link EnvInput} which describes the file to load.
    */
   private EnvInput envInput;

   /**
    * The instantiated {@link ProblemInitializer} used during the loading process.
    */
   private ProblemInitializer problemInitializer;

   /**
    * The instantiated {@link InitConfig} which provides access to the loaded source elements and specifications.
    */
   private InitConfig initConfig;

   /**
    * The instantiate proof or {@code null} if no proof was instantiated during loading process.
    */
   private Proof proof;

   private static String INDEX_FILE = "automaticInfFlow.txt";

   private static String IF_INDEX_FILE = "automaticMacroInfFlow.txt";

   /**
    * Constructor.
    * @param file The file or folder to load.
    * @param classPath The optional class path entries to use.
    * @param bootClassPath An optional boot class path.
    * @param profileOfNewProofs The {@link Profile} to use for new {@link Proof}s.
    * @param mediator The {@link KeYMediator} to use.
    * @param askUiToSelectAProofObligationIfNotDefinedByLoadedFile {@code true} to call {@link UserInterface#selectProofObligation(InitConfig)} if no {@link Proof} is defined by the loaded proof or {@code false} otherwise which still allows to work with the loaded {@link InitConfig}.
    */
   public DefaultProblemLoader(File file, 
                               List<File> classPath, 
                               File bootClassPath,
                               Profile profileOfNewProofs, 
                               KeYMediator mediator,
                               boolean askUiToSelectAProofObligationIfNotDefinedByLoadedFile,
                               Properties poPropertiesToForce) {
      assert mediator != null;
      this.file = file;
      this.classPath = classPath;
      this.bootClassPath = bootClassPath;
      this.mediator = mediator;
      this.profileOfNewProofs = profileOfNewProofs != null ? profileOfNewProofs : AbstractProfile.getDefaultProfile();
      this.askUiToSelectAProofObligationIfNotDefinedByLoadedFile = askUiToSelectAProofObligationIfNotDefinedByLoadedFile;
      this.poPropertiesToForce = poPropertiesToForce;
   }

   /**
    * Executes the loading process and tries to instantiate a proof
    * and to re-apply rules on it if possible.
    * @throws ProofInputException Occurred Exception.
    * @throws IOException Occurred Exception.
    */
   public ProblemLoaderException load() throws ProblemLoaderException {
       // TODO: returns AND throws exceptions?
       try {
           // Read environment
           boolean oneStepSimplifier =
                   ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().oneStepSimplification();
           ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().setOneStepSimplification(true);
           envInput = createEnvInput();
           problemInitializer = createProblemInitializer();
           initConfig = createInitConfig();
           // Read proof obligation settings
           LoadedPOContainer poContainer = createProofObligationContainer();
           try {
               if (poContainer == null) {
                   if (askUiToSelectAProofObligationIfNotDefinedByLoadedFile) {
                      if (mediator.getUI().selectProofObligation(initConfig)) {
                         return null;
                      } else {
                         return new ProblemLoaderException(this, "Aborted.");
                      }
                   }
                   else {
                      return null; // Do not instantiate any proof but allow the user of the DefaultProblemLoader to access the loaded InitConfig.
                   }
               }
               // Create proof and apply rules again if possible
               proof = createProof(poContainer);
               if (proof != null) {
                   replayProof(proof);
               }
               // this message is propagated to the top level in console mode
               return null; // Everything fine
         }         
         finally {
               ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings()
                                   .setOneStepSimplification(oneStepSimplifier);
               getMediator().resetNrGoalsClosedByHeuristics();
               if (poContainer != null && poContainer.getProofOblInput() instanceof KeYUserProblemFile) {
                   ((KeYUserProblemFile)poContainer.getProofOblInput()).close();
               }
           }
       }
       catch (ProblemLoaderException e) {
           throw e;
       }
       catch (ProofInputException pie) {
           // try to resolve error message
           Throwable c0 = pie.getCause();
           if (c0 instanceof ExceptionHandlerException) {
               c0 = c0.getCause();    
           }
           if (c0 instanceof org.antlr.runtime.MissingTokenException) {
               final org.antlr.runtime.MissingTokenException mte = (org.antlr.runtime.MissingTokenException) c0;
               final org.antlr.runtime.Token occurrence = mte.token;
               // TODO: other commonly missed tokens
               final String token = mte.expecting == KeYLexer.SEMI? "semicolon": "token id "+mte.expecting;
               final String msg = "Syntax error: missing "+token+" at "+
                               occurrence.getText()+" statement ("+mte.input.getSourceName()
                               +":"+mte.line+")";
               throw new ProblemLoaderException(this, msg, mte);
               // TODO other ANTLR exceptions
           } else {
               throw new ProblemLoaderException(this, "Loading proof input failed", pie);
           }
       }
       catch (Exception e) { // TODO give more specific exception message
           throw new ProblemLoaderException(this, e);
       }
   }

   private File chooseFile(ContractPO po) {
       final String fName;
       if (po instanceof InfFlowPO) {
           fName = IF_INDEX_FILE;
       } else {
           fName = INDEX_FILE;
       }
       return new File("examples/index/", fName);
   }

   private void writeToFile(String path, File file) {
       String examplesPath = "examples/";
       boolean inExampleDir = 0 <= path.indexOf(examplesPath);
       String prefix =
               file.getName().endsWith(IF_INDEX_FILE) && path.contains("insecure") ?
                       "notprovable: " : "provable: ";
       path = "./" +
               (inExampleDir ?
                       path.substring(path.indexOf(examplesPath) + examplesPath.length()) : path);
       try {
           PrintWriter w = new PrintWriter(new BufferedWriter(new FileWriter(file, true)));
           w.println(prefix + path);
           w.close();
       } catch (IOException e) {
           e.printStackTrace();
       }
   }

   private ImmutableSet<String> getFileNames(File file) {
       ImmutableSet<String> result = DefaultImmutableSet.<String>nil();
       boolean foundValidJavaFiles = false;
       if (file.isDirectory()) {
           for (File f: file.listFiles()) {
               if (!f.isDirectory() && f.getName().endsWith(".java")) {
                   foundValidJavaFiles = true;
                   result = result.add(f.getName().substring(0, f.getName().indexOf(".")));
               }
           }
       } else if (file.getName().endsWith(".java")) {
           foundValidJavaFiles = true;
           result = result.add(getFile().getName()
                   .substring(0, getFile().getName().indexOf(".")));
       }
       if (!foundValidJavaFiles) {
           throw new IllegalArgumentException(
                   "Specified file is no valid directory or java-file!");
       }
       return result;
   }

   public Throwable saveAll() {
       ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().setOneStepSimplification(true);
       try {
           envInput = createEnvInput();
           problemInitializer = createProblemInitializer();
           initConfig = createInitConfig();
           final SpecificationRepository specRepos =
                   initConfig.getServices().getSpecificationRepository();
           final UserInterface ui = getMediator().getUI();
           final JavaInfo javaInfo = initConfig.getServices().getJavaInfo();
           ImmutableSet<String> fileNames = getFileNames(getFile());
           for (KeYJavaType kjt: javaInfo.getAllKeYJavaTypes()) {
               if (!fileNames.contains(kjt.getName())) {
                   // skip
               } else {
                   for (IObserverFunction target: specRepos.getContractTargets(kjt)) {
                       for (Contract c: specRepos.getContracts(kjt, target)) {
                           final ContractPO po = c.createProofObl(initConfig);
                           po.readProblem();
                           for (Proof p: po.getPO().getProofs()) {
                               p.removeInfFlowProofSymbols();
                               p.setEnv(new ProofEnvironment(initConfig));
                               ui.getMediator().getSelectionModel().setProof(p);
                               specRepos.registerProof(po, p);
                               final File poFile = ui.saveProof(p, ".key");
                               final String path = poFile.getPath();
                               writeToFile(path, chooseFile(po));
                           }
                       }
                   }
               }
           }
       } catch (Throwable e) {
           return new ProblemLoaderException(this, e);
       }
       return null;
   }

   /**
    * Instantiates the {@link EnvInput} which represents the file to load.
    * @return The created {@link EnvInput}.
    * @throws IOException Occurred Exception.
    */
   protected EnvInput createEnvInput() throws IOException {

      final String filename = file.getName();

      if (filename.endsWith(".java")) {
         // java file, probably enriched by specifications
         if (file.getParentFile() == null) {
            return new SLEnvInput(".", classPath, bootClassPath, profileOfNewProofs);
         }
         else {
            return new SLEnvInput(file.getParentFile().getAbsolutePath(),
                  classPath, bootClassPath, profileOfNewProofs);
         }
      }
      else if (filename.endsWith(".key") || filename.endsWith(".proof")) {
         // KeY problem specification or saved proof
         return new KeYUserProblemFile(filename, file, mediator.getUI(), profileOfNewProofs);

      }
      else if (file.isDirectory()) {
         // directory containing java sources, probably enriched
         // by specifications
         return new SLEnvInput(file.getPath(), classPath, bootClassPath, profileOfNewProofs);
      }
      else {
         if (filename.lastIndexOf('.') != -1) {
            throw new IllegalArgumentException("Unsupported file extension \'"
                  + filename.substring(filename.lastIndexOf('.'))
                  + "\' of read-in file " + filename
                  + ". Allowed extensions are: .key, .proof, .java or "
                  + "complete directories.");
         }
         else {
            throw new FileNotFoundException("File or directory\n\t " + filename
                  + "\n not found.");
         }
      }
   }

   /**
    * Instantiates the {@link ProblemInitializer} to use.
    * @param registerProof Register loaded {@link Proof}
    * @return The {@link ProblemInitializer} to use.
    */
   protected ProblemInitializer createProblemInitializer() {
      UserInterface ui = mediator.getUI();
      return new ProblemInitializer(ui,
                                    new Services(envInput.getProfile(), 
                                          mediator.getExceptionHandler()),
                                    ui);
   }

   /**
    * Creates the {@link InitConfig}.
    * @return The created {@link InitConfig}.
    * @throws ProofInputException Occurred Exception.
    */
   protected InitConfig createInitConfig() throws ProofInputException {
      return problemInitializer.prepare(envInput);
   }

   /**
    * Creates a {@link LoadedPOContainer} if available which contains
    * the {@link ProofOblInput} for which a {@link Proof} should be instantiated.
    * @return The {@link LoadedPOContainer} or {@code null} if not available.
    * @throws IOException Occurred Exception.
    */
   protected LoadedPOContainer createProofObligationContainer() throws IOException {
      final String chooseContract;
      final String proofObligation;
      if (envInput instanceof KeYFile) {
          KeYFile keyFile = (KeYFile)envInput;
          chooseContract = keyFile.chooseContract();
          proofObligation = keyFile.getProofObligation();
      }
      else {
          chooseContract = null;
          proofObligation = null;
      }
      // Instantiate proof obligation
      if (envInput instanceof ProofOblInput && chooseContract == null && proofObligation == null) {
          return new LoadedPOContainer((ProofOblInput)envInput);
      }
      else if (chooseContract != null && chooseContract.length() > 0) {
          int proofNum = 0;
          String baseContractName = null;
          int ind = -1;
          for (String tag : FunctionalOperationContractPO.TRANSACTION_TAGS.values()) {
              ind = chooseContract.indexOf("." + tag);
              if (ind > 0) {
                  break;
              }
              proofNum++;
          }
          if (ind == -1) {
              baseContractName = chooseContract;
              proofNum = 0;
          }
          else {
              baseContractName = chooseContract.substring(0, ind);
          }
          final Contract contract = initConfig.getServices().getSpecificationRepository().getContractByName(baseContractName);
          if (contract == null) {
              throw new RuntimeException("Contract not found: " + baseContractName);
          }
          else {
              return new LoadedPOContainer(contract.createProofObl(initConfig), proofNum);
          }
      }
      else if (proofObligation != null && proofObligation.length() > 0) {
          // Load proof obligation settings
          final Properties properties = new Properties();
          properties.load(new ByteArrayInputStream(proofObligation.getBytes()));
          properties.setProperty(IPersistablePO.PROPERTY_FILENAME, file.getAbsolutePath());
          if (poPropertiesToForce != null) {
              properties.putAll(poPropertiesToForce);
           }
          String poClass = properties.getProperty(IPersistablePO.PROPERTY_CLASS);
          if (poClass == null || poClass.isEmpty()) {
              throw new IOException("Proof obligation class property \"" + IPersistablePO.PROPERTY_CLASS + "\" is not defiend or empty.");
          }
          try {
              // Try to instantiate proof obligation by calling static method: public static LoadedPOContainer loadFrom(InitConfig initConfig, Properties properties) throws IOException
              Class<?> poClassInstance = Class.forName(poClass);
              Method loadMethod = poClassInstance.getMethod("loadFrom", InitConfig.class, Properties.class);
              return (LoadedPOContainer)loadMethod.invoke(null, initConfig, properties);
          }
          catch (Exception e) {
              throw new IOException("Can't call static factory method \"loadFrom\" on class \"" + poClass + "\".", e);
          }
      }
      else {
          return null;
      }
   }

   /**
    * Creates a {@link Proof} for the given {@link LoadedPOContainer} and
    * tries to apply rules again.
    * @param poContainer The {@link LoadedPOContainer} to instantiate a {@link Proof} for.
    * @return The instantiated {@link Proof}.
    * @throws ProofInputException Occurred Exception.
    */
   protected Proof createProof(LoadedPOContainer poContainer) throws ProofInputException {
      ProofAggregate proofList = problemInitializer.startProver(initConfig, poContainer.getProofOblInput());
      
      mediator.getUI().createProofEnvironmentAndRegisterProof(poContainer.getProofOblInput(), proofList, initConfig);

      return proofList.getProof(poContainer.getProofNum());
   }

   protected void replayProof(Proof proof) throws ProofInputException {
      mediator.setProof(proof);

      mediator.stopInterface(true); // first stop (above) is not enough

      String status = "";
      List<Throwable> errors = null;
      if (envInput instanceof KeYUserProblemFile) {
          DefaultProofFileParser parser = new DefaultProofFileParser(this, proof,
                                                              mediator);
         problemInitializer.tryReadProof(parser, (KeYUserProblemFile) envInput);
         status = parser.getStatus();
         errors = parser.getErrors();
      }

      if ("".equals(status)) {
          mediator.getUI().resetStatus(this);
      } else {
          mediator.getUI().reportStatus(this, status);
          if (errors != null &&
                  !errors.isEmpty()) {
              throw new ProblemLoaderException(this,
                      "Proof could only be loaded partially.\n" +
                      "In summary " + errors.size() +
                      " not loadable rule application(s) have been detected.\n" +
                      "The first one:\n"+errors.get(0).getMessage(), errors.get(0));
          }
      }
   }

   /**
    * Returns the file or folder to load.
    * @return The file or folder to load.
    */
   public File getFile() {
      return file;
   }

   /**
    * Returns the optional class path entries to use.
    * @return The optional class path entries to use.
    */
   public List<File> getClassPath() {
      return classPath;
   }

   /**
    * Returns the optional boot class path.
    * @return The optional boot class path.
    */
   public File getBootClassPath() {
      return bootClassPath;
   }

   /**
    * Returns the {@link KeYMediator} to use.
    * @return The {@link KeYMediator} to use.
    */
   public KeYMediator getMediator() {
      return mediator;
   }

   /**
    * Returns the instantiated {@link EnvInput} which describes the file to load.
    * @return The instantiated {@link EnvInput} which describes the file to load.
    */
   public EnvInput getEnvInput() {
      return envInput;
   }

   /**
    * Returns the instantiated {@link ProblemInitializer} used during the loading process.
    * @return The instantiated {@link ProblemInitializer} used during the loading process.
    */
   public ProblemInitializer getProblemInitializer() {
      return problemInitializer;
   }

   /**
    * Returns the instantiated {@link InitConfig} which provides access to the loaded source elements and specifications.
    * @return The instantiated {@link InitConfig} which provides access to the loaded source elements and specifications.
    */
   public InitConfig getInitConfig() {
      return initConfig;
   }

   /**
    * Returns the instantiate proof or {@code null} if no proof was instantiated during loading process.
    * @return The instantiate proof or {@code null} if no proof was instantiated during loading process.
    */
   public Proof getProof() {
      return proof;
   }
}
