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

package de.uka.ilkd.key.taclettranslation.lemma;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Properties;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.IPersistablePO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.taclettranslation.lemma.TacletSoundnessPOLoader.LoaderListener;
import de.uka.ilkd.key.taclettranslation.lemma.TacletSoundnessPOLoader.TacletFilter;
import de.uka.ilkd.key.taclettranslation.lemma.TacletSoundnessPOLoader.TacletInfo;

/**
 * The Class TacletProofObligationInput is a special purpose proof obligations
 * for taclet proofs.
 * 
 * A proof for a KeY system-taclet can thus be reloaded and checked against the
 * current environment.
 * 
 * @author mattias ulbrich
 */
public class TacletProofObligationInput implements ProofOblInput, IPersistablePO {

    private String tacletName;
    private ProofAggregate proofObligation;

    // The following may all possibly be null
    private String definitionFile;
    private String tacletFile;
    private String[] axiomFiles;
    private String baseDir;

    /**
     * This filter is used to filter out precisely that taclet which has the
     * required name.
     */
    private TacletFilter filter = new TacletFilter() {
        @Override 
        public ImmutableSet<Taclet> filter(List<TacletInfo> taclets) {
            Name name = new Name(tacletName);
            for (TacletInfo tacletInfo : taclets) {
                if(tacletInfo.getTaclet().name().equals(name)) {
                    return DefaultImmutableSet.<Taclet>nil().add(tacletInfo.getTaclet());
                }
            }
            return DefaultImmutableSet.nil();
        }
    };

    /**
     * This listener communicates with the PO loader.
     */
    private LoaderListener listener = new LoaderListener() {

        @Override 
        public void stopped(Throwable exception) {
            System.err.println("Exception while loading proof obligation for taclet:");
            exception.printStackTrace();
        }

        @Override 
        public void stopped(ProofAggregate p, ImmutableSet<Taclet> taclets, boolean addAsAxioms) {
            proofObligation = p;
        }

        @Override 
        public void started() {
        }

        @Override 
        public void resetStatus(Object sender) {
        }

        @Override 
        public void reportStatus(Object sender, String string) {
        }

        @Override 
        public void progressStarted(Object sender) {
        }
    };
   
    private final InitConfig environmentConfig;
 

    /**
     * Instantiates a new taclet proof obligation input object.
     * 
     * @param tacletName
     *            the name of the taclet which is to be created
     * @param initConfig
     *            the initconfig under which the PO is to be examined
     */
    public TacletProofObligationInput(String tacletName, InitConfig initConfig) {
        this.tacletName = tacletName;
        this.environmentConfig = initConfig;
    }

    /*
     * Fill in only the necessary info.
     */
    @Override 
    public void fillSaveProperties(Properties properties) throws IOException {
        properties.setProperty(IPersistablePO.PROPERTY_CLASS, getClass().getCanonicalName());
        properties.setProperty(IPersistablePO.PROPERTY_NAME, name());

        // TODO MU ----- make the file names relative
        // MiscTools.makeFilenamesRelative. However ... I need the store save name ...

        if (tacletFile != null) {
            properties.setProperty("tacletFile", tacletFile);
        }
        if (definitionFile != null) {
            properties.setProperty("definitionFile", definitionFile);
        }
        if (axiomFiles != null) {
            for (int i = 0; i < axiomFiles.length; i++) {
                String name = "axiomFile" + (i == 0 ? "" : (i + 1));
                properties.setProperty(name, axiomFiles[i]);
            }
        }
    }

    @Override 
    public String name() {
        return tacletName;
    }

    /*
     * use the TacletLoader and TacletSoundlessPOLoader to generate the PO.
     */
    @Override 
    public void readProblem() throws ProofInputException {
        TacletLoader loader = null;
        
        if (tacletFile == null) {
            // prove a KeY taclet
            loader = new TacletLoader.KeYsTacletsLoader(null, null, environmentConfig.getProfile());
        } else {
            final ProblemInitializer problemInitializer =
                    new ProblemInitializer( environmentConfig.getProfile());
            // bugfix: All files are loaded relative to the basedir of the loaded file
            loader = new TacletLoader.TacletFromFileLoader(null, null, problemInitializer,
                    new File(baseDir, definitionFile), new File(baseDir, tacletFile), 
                    fileCollection(axiomFiles), environmentConfig);
        }

        TacletSoundnessPOLoader poloader =
                new TacletSoundnessPOLoader(listener, filter, true, loader, loader.getProofEnvForTaclets().getInitConfigForEnvironment(), true);

        poloader.startSynchronously();
        if(proofObligation == null) {
            throw new ProofInputException("Cannot instantiate the proof obligation for taclet '" + 
                    tacletName + "'. Is it defined (in the specified tacletFile?)");
            }
    }


    private Collection<File> fileCollection(String[] strings) {
        ArrayList<File> result = new ArrayList<File>();
        for (int i = 0; i < strings.length; i++) {
            result.add(new File(baseDir, strings[i]));
        }
        return result;
    }

    /*
     * just deliver the precalculated PO
     */
    @Override 
    public ProofAggregate getPO() throws ProofInputException {
        assert proofObligation != null : 
            "readProblem should have been called first";
        return proofObligation;
    }

    @Override
    public boolean implies(ProofOblInput po) {
        return this == po;
    }

    public static LoadedPOContainer loadFrom(InitConfig initConfig, Properties properties) {
        String tacletName = properties.getProperty(PROPERTY_NAME);
        // This string is parsed by "proveRules.pl"
        System.out.println("Proof obligation for taclet: " + tacletName);
        TacletProofObligationInput proofOblInput =
                new TacletProofObligationInput(tacletName, initConfig);
        proofOblInput.setLoadInfo(properties);
        return new LoadedPOContainer(proofOblInput);
    }

    private void setLoadInfo(Properties properties) {
        this.baseDir = new File(properties.getProperty(IPersistablePO.PROPERTY_FILENAME)).getParent();
        this.tacletFile = properties.getProperty("tacletFile");
        this.definitionFile = properties.getProperty("definitionFile");
        List<String> axioms = new ArrayList<String>();
        String name = "axiomFile";
        String axFile = properties.getProperty(name);
        while (axFile != null) {
            axioms.add(axFile);
            name = "axiomFile" + (axioms.size() + 1);
            axFile = properties.getProperty(name);
        }
        this.axiomFiles = axioms.toArray(new String[axioms.size()]);
    }

    public void setLoadInfo(File tacletFile, File definitionFile,
            Collection<File> axiomFiles) {
        this.tacletFile = tacletFile.toString();
        this.definitionFile = definitionFile.toString();
        this.axiomFiles = new String[axiomFiles.size()];

        int i = 0;
        for (File file : axiomFiles) {
            this.axiomFiles[i] = file.toString();
            i++;
        }
    }
}