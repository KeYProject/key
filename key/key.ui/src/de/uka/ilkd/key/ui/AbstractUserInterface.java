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

import java.io.File;
import java.util.List;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.KeYFileChooser;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.SkipMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.ProverTaskListener;
import de.uka.ilkd.key.proof.TaskFinishedInfo;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.ProblemLoader;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.proof.mgt.ProofEnvironmentEvent;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;

public abstract class AbstractUserInterface implements UserInterface {

    private static String INDEX_FILE = "automaticJAVADL.txt";
    private static String IF_INDEX_FILE = "automaticMacroInfFlow.txt";

    private ProofMacro autoMacro = new SkipMacro();
    protected boolean saveOnly = false;

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


   protected static Pair<File, String> fileName(Proof proof, String fileExtension) {
       // TODO: why do we use GUI components here?
       final KeYFileChooser jFC = KeYFileChooser.getFileChooser("Choose filename to save proof");

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