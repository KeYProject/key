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

package de.uka.ilkd.key.ui;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.List;
import java.util.Properties;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.ProverTaskListener;
import de.uka.ilkd.key.core.TaskFinishedInfo;
import de.uka.ilkd.key.gui.KeYFileChooser;
import de.uka.ilkd.key.gui.configuration.ProofIndependentSettings;
import de.uka.ilkd.key.gui.utilities.GuiUtilities;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.macros.SkipMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.InfFlowPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader;
import de.uka.ilkd.key.proof.io.ProblemLoader;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.io.SingleThreadProblemLoader;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.proof.mgt.ProofEnvironmentEvent;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;

public abstract class AbstractUserInterface implements UserInterface {

    private static String INDEX_FILE = "automaticJAVADL.txt";
    private static String IF_INDEX_FILE = "automaticMacroInfFlow.txt";

    private ProofMacro autoMacro = new SkipMacro();
    protected boolean saveOnly = false;
    private boolean autoSave =
            ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().autoSave();

    private ProverTaskListener pml = null;

    protected ProblemLoader getProblemLoader(File file, List<File> classPath,
                                             File bootClassPath, KeYMediator mediator) {
        final ProblemLoader pl =
                new ProblemLoader(file, classPath, bootClassPath,
                                  AbstractProfile.getDefaultProfile(), false, mediator, true, null, this);
        return pl;
    }

    @Override
    public  IBuiltInRuleApp completeBuiltInRuleApp(IBuiltInRuleApp app, Goal goal, boolean forced) {
        app = forced? app.forceInstantiate(goal): app.tryToInstantiate(goal);
        // cannot complete that app
        return app.complete() ? app : null;
    }

    public void setSaveOnly(boolean s) {
        this.saveOnly = s;
    }

    public void noAutoSave() {
        this.autoSave = false;
    }

    public void resetAutoSave() {
        this.autoSave =
                ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().autoSave();
    }

    public boolean autoSave() {
        return autoSave;
    }

    public boolean isSaveOnly() {
        return this.saveOnly;
    }

    public void setMacro(ProofMacro macro) {
        assert macro != null;
        this.autoMacro = macro;
    }

    public ProofMacro getMacro() {
        return this.autoMacro;
    }

    public boolean macroChosen() {
        return !(getMacro() instanceof SkipMacro);
    }

    @Override
    public final ProverTaskListener getListener() {
        if (this.pml == null) {
            this.pml = new ProofMacroListenerAdapter();
        }
        return new CompositePTListener(this, pml);
    }

    @Override
    public ProofEnvironment createProofEnvironmentAndRegisterProof(ProofOblInput proofOblInput,
          ProofAggregate proofList, InitConfig initConfig) {
       final ProofEnvironment env = new ProofEnvironment(initConfig);
       env.addProofEnvironmentListener(this);
       env.registerProof(proofOblInput, proofList);
       return env;
    }

   public boolean applyMacro() {
        assert macroChosen();
        final ProofMacro macro = getMacro();
        if (macro.canApplyTo(getMediator(), null)) {
            Debug.out("[ APPLY " + getMacro().getClass().getSimpleName() + " ]");
            Proof proof = getMediator().getSelectedProof();
            TaskFinishedInfo info = ProofMacroFinishedInfo.getDefaultInfo(macro, proof);
            ProverTaskListener ptl = getListener();
            try {
                getMediator().stopInterface(true);
                getMediator().setInteractive(false);
                ptl.taskStarted(macro.getName(), 0);
                synchronized(macro) {
                    // wait for macro to terminate
                    info = macro.applyTo(getMediator(), null, ptl);
                }
            } catch(InterruptedException ex) {
                Debug.out("Proof macro has been interrupted:");
                Debug.out(ex);
            } finally {
                ptl.taskFinished(info);
                getMediator().setInteractive(true);
                getMediator().startInterface(true);
            }
            return true;
        } else {
            System.out.println(macro.getClass().getSimpleName() + " not applicable!");
        }
        return false;
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
       String prefix = file.getName().endsWith(IF_INDEX_FILE) && path.contains("insecure") ?
               "notprovable: " : "provable: ";
       path = "./" + (inExampleDir ?
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
       String name = file.getName();
       if (file.isDirectory()) {
           for (File f: file.listFiles()) {
               name = f.getName();
               if (!f.isDirectory() && name.endsWith(".java")) {
                   foundValidJavaFiles = true;
                   result = result.add(name.substring(0, name.indexOf(".")));
               }
           }
       } else if (name.endsWith(".java")) {
           foundValidJavaFiles = true;
           result = result.add(name.substring(0, name.indexOf(".")));
       }
       if (!foundValidJavaFiles) {
           throw new IllegalArgumentException(
                           "Specified file is no valid directory or java-file!");
       }
       return result;
   }

   public void saveAll(InitConfig initConfig, File file) throws ProofInputException {
       final SpecificationRepository specRepos =
               initConfig.getServices().getSpecificationRepository();
       for (KeYJavaType kjt: initConfig.getServices().getJavaInfo().getAllKeYJavaTypes()) {
           if (!getFileNames(file).contains(kjt.getName())) {
               // skip
           } else {
               for (IObserverFunction target: specRepos.getContractTargets(kjt)) {
                   for (Contract c: specRepos.getContracts(kjt, target)) {
                       final ContractPO po = c.createProofObl(initConfig);
                       po.readProblem();
                       for (Proof p: po.getPO().getProofs()) {
                           p.removeInfFlowProofSymbols();
                           p.setEnv(new ProofEnvironment(initConfig));
                           getMediator().getSelectionModel().setProof(p);
                           specRepos.registerProof(po, p);
                           final File poFile = saveProof(p, ".key");
                           final String path = poFile.getPath();
                           writeToFile(path, chooseFile(po));
                       }
                   }
               }
           }
       }
   }

   protected static Pair<File, String> fileName(Proof proof, String fileExtension) {
       final KeYFileChooser jFC = GuiUtilities.getFileChooser("Choose filename to save proof");

       File selectedFile = null;
       if (proof != null) {
          selectedFile = proof.getProofFile();
       }
       // Suggest default file name if required
       final String defaultName;
       if (selectedFile == null) {
           defaultName = MiscTools.toValidFileName(proof.name().toString()) + fileExtension;
           selectedFile = new File(jFC.getCurrentDirectory(), defaultName);
       } else if (selectedFile.getName().endsWith(".proof") && fileExtension.equals(".proof")) {
           defaultName = selectedFile.getName();
       } else {
           String proofName = proof.name().toString();
           if (proofName.endsWith(".key")) {
               proofName = proofName.substring(0, proofName.lastIndexOf(".key"));
           } else if (proofName.endsWith(".proof")) {
               proofName = proofName.substring(0, proofName.lastIndexOf(".proof"));
           }
           defaultName = MiscTools.toValidFileName(proofName) + fileExtension;
           selectedFile = new File(selectedFile.getParentFile(), defaultName);
       }
       return new Pair<File, String>(selectedFile, defaultName);
   }

    /**
     * {@inheritDoc}
     */
    @Override
    public AbstractProblemLoader load(Profile profile,
                                     File file,
                                     List<File> classPath,
                                     File bootClassPath,
                                     Properties poPropertiesToForce,
                                     boolean forceNewProfileOfNewProofs) throws ProblemLoaderException {
       AbstractProblemLoader loader = null;
       try {
          getMediator().stopInterface(true);
          loader = new SingleThreadProblemLoader(file, classPath, bootClassPath, profile, forceNewProfileOfNewProofs,
                                                 getMediator(), false, poPropertiesToForce);
          loader.load();
          return loader;
       }
       catch(ProblemLoaderException e) {
           if (loader != null && loader.getProof() != null) {
               loader.getProof().dispose();
           }
           // rethrow that exception
           throw e;
       }
       catch (Throwable e) {
           if (loader != null && loader.getProof() != null) {
               loader.getProof().dispose();
           }
           throw new ProblemLoaderException(loader, e);
       }
       finally {
          getMediator().startInterface(true);
       }
    }

   /**
     * {@inheritDoc}
     */
    @Override
    public Proof createProof(InitConfig initConfig, ProofOblInput input) throws ProofInputException {
       ProblemInitializer init = createProblemInitializer(initConfig.getProfile());
       ProofAggregate proofList = init.startProver(initConfig, input);
       createProofEnvironmentAndRegisterProof(input, proofList, initConfig);
       return proofList.getFirstProof();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void startAndWaitForAutoMode(Proof proof) {
       startAutoMode(proof);
       waitWhileAutoMode();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void startAutoMode(Proof proof) {
       KeYMediator mediator = getMediator();
       mediator.setProof(proof);
       mediator.startAutoMode();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void startAutoMode(Proof proof, ImmutableList<Goal> goals) {
       KeYMediator mediator = getMediator();
       mediator.setProof(proof);
       mediator.startAutoMode(goals);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void stopAutoMode() {
       getMediator().stopAutoMode();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void waitWhileAutoMode() {
       while (getMediator().isInAutoMode()) { // Wait until auto mode has stopped.
          try {
             Thread.sleep(100);
          }
          catch (InterruptedException e) {
          }
       }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void notifyAutoModeBeingStarted() {
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void notifyAutomodeStopped() {
    }

    @Override
    public void proofUnregistered(ProofEnvironmentEvent event) {
       if (event.getSource().getProofs().isEmpty()) {
          event.getSource().removeProofEnvironmentListener(this);
       }
    }

    abstract protected void macroStarted(String message, int size);
    abstract protected void macroFinished(TaskFinishedInfo info);


    private class ProofMacroListenerAdapter implements ProverTaskListener {

        @Override
        public void taskStarted(String message, int size) {
            macroStarted(message, size);
        }

        @Override
        public void taskProgress(int position) {
            // not needed yet
        }

        @Override
        public void taskFinished(TaskFinishedInfo info) {
            macroFinished(info);
        }
    }
}