//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//Universitaet Koblenz-Landau, Germany
//Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.init;

import java.io.File;
import java.util.HashMap;
import java.util.Iterator;

import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.mgt.*;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.soundness.POBuilder;
import de.uka.ilkd.key.rule.soundness.POSelectionDialog;
import de.uka.ilkd.key.rule.soundness.SVSkolemFunction;
import de.uka.ilkd.key.util.ProgressMonitor;

public class TacletSoundnessPO extends KeYUserProblemFile 
implements ProofOblInput{
    
    public boolean askUserForEnvironment () {
        return false;
    }
    
    private ProofAggregate proof;
    
    private NoPosTacletApp[] app;
    
    public TacletSoundnessPO (String name, File file, 
            ProgressMonitor monitor) {
        super ( name, file, monitor, true );
    }
    
    /** returns the proof obligation term as result of the proof obligation
     * input. If there is still no input available because nothing has
     * been read yet null is returned.
     */
    public ProofAggregate getPO () {
        return proof;
    }
    
    public NoPosTacletApp[] getTaclets () {
        return app;
    }
    
    /** starts reading the input and modifies the InitConfig of this 
     * object with respect to the given modification
     * strategy. 
     */
    public void readProblem(ModStrategy mod) throws ProofInputException {
        assert initConfig != null;
        final InitConfig old = initConfig;
        initConfig = old.copy ();
        initConfig.getServices().setJavaInfo(old.getServices().getJavaInfo());
        
        // ensure that only the new taclets of the lemma file are presented to
        // the user
        initConfig.setTaclets ( SetAsListOfTaclet.EMPTY_SET );
        initConfig.setTaclet2Builder ( new HashMap () );
        
        SetOfTaclet newTaclets=null;
        try {
            super.read ( ModStrategy.NO_VARS_FUNCS); // actually this
            // reads the
            // complete
            // problem, which is not really
            // needed; could be optimized
            newTaclets = initConfig.getTaclets();
        } finally {
            initConfig=old;
        }
        // this ensures that necessary Java types are loaded
        initConfig.getServices().getJavaInfo().readJavaBlock("{}");
        
        IteratorOfTaclet it = newTaclets.iterator();
        SetOfNoPosTacletApp newTacApps = SetAsListOfNoPosTacletApp.EMPTY_SET;
        while (it.hasNext()) {
            newTacApps = newTacApps.add
            (NoPosTacletApp.createNoPosTacletApp(it.next()));
        }
        
        final POSelectionDialog dialog = new POSelectionDialog 
        ( Main.getInstance().mediator (),
                newTacApps);
        
        app = dialog.getSelectedTaclets ();
                
        if ( app == null || app.length==0)
            throw new ProofInputException ( "No taclet was selected" );
        
        ProofAggregate[] singleProofs = new ProofAggregate[app.length];
        ProofEnvironment env = initConfig.getProofEnv();
        for (int i=0; i<app.length; i++) {
            final POBuilder pob = new POBuilder ( app[i], initConfig.getServices() );
            pob.build ();
            Main.getInstance()
                .mediator()
                .getSelectedGoal()
                .addTaclet(app[i].taclet(), 
                           app[i].instantiations(), 
                           app[i].constraint(),
                           false);
            
            updateNamespaces ( pob );
            String name = app.length==1 ? name() : app[i].taclet().name().toString();
            singleProofs[i] = ProofAggregate.createProofAggregate
            	(new Proof(name,
                    pob.getPOTerm(),
                    createProofHeader(),
                    initConfig.createTacletIndex(),
                    initConfig.createBuiltInRuleIndex(),
                    initConfig.getServices()),
                    name);            
        }
        if (app.length==1) {
            proof = singleProofs[0];
        } else {
            proof = ProofAggregate.createProofAggregate(singleProofs, name());
        }
        env.registerProof(this, proof);
    }
    
    
    private void updateNamespaces (POBuilder p_pob) {
        NamespaceSet globalNss = initConfig.namespaces();
        Namespace funcNs = globalNss.functions ();
        
        {
            final IteratorOfNamed it =
                p_pob.getFunctions ().allElements ().iterator ();
            while ( it.hasNext () )
                funcNs.add ( it.next () );
        }
        
//      {
//      final IteratorOfTacletApp it = p_pob.getTaclets ().iterator ();
//      while ( it.hasNext () )
//      p_tacletIndex.add((NoPosTacletApp)it.next ());
//      }
    }
    
    
    
    /** set the initial configuration used to read an input. It may become
     * modified during reading depending on the modification strategy used
     * for reading.
     */
    public void setInitConfig(InitConfig i) {
        initConfig = i;
    }
    
    public void readActivatedChoices() throws ProofInputException { 
	//nothing to do 
    }
    
    /** reads the include section and returns an Includes object.  
     */
    public Includes readIncludes() throws ProofInputException {
        return new Includes ();
    }
    
    /** returns the name of the proof obligation input.
     */
    public String name() {
        if (app==null) return "Taclet proof obligation";
        return "Proof obligation(s) for "+file;
    }   
    
    
    /**
     * Creates declarations necessary to save/load proof in textual form.
     */
    private String createProofHeader() throws ProofInputException {
        String result = "";
        
        //includes of taclet file must be copied        
        Iterator it = super.readIncludes().getIncludes().iterator();
        while(it.hasNext()) {            
            String fileName = (String) it.next();
            result += "\\include \"" + fileName + "\";\n";
        }
        
        //created SVSkolemFunctions must be declared 
        result += "\n\\functions {\n";
        IteratorOfNamed it2 
            = initConfig.namespaces().functions().allElements().iterator();
        while(it2.hasNext()) {
            Function f = (Function) it2.next();
            if(f instanceof SVSkolemFunction) {
                result += f.proofToString();
            }
        }
        result += "}\n\n";
                
        return result;
    }
}
