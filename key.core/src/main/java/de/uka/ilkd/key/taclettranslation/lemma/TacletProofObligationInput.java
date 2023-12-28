/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.taclettranslation.lemma;

import java.io.File;
import java.io.IOException;
import java.util.*;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.*;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.taclettranslation.lemma.TacletSoundnessPOLoader.LoaderListener;
import de.uka.ilkd.key.taclettranslation.lemma.TacletSoundnessPOLoader.TacletFilter;
import de.uka.ilkd.key.taclettranslation.lemma.TacletSoundnessPOLoader.TacletInfo;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * The Class TacletProofObligationInput is a special purpose proof obligations for taclet proofs.
 * <p>
 * A proof for a KeY system-taclet can thus be reloaded and checked against the current environment.
 *
 * @author mattias ulbrich
 */
public class TacletProofObligationInput implements ProofOblInput, IPersistablePO {
    private static final Logger LOGGER = LoggerFactory.getLogger(TacletProofObligationInput.class);
    public static final String AXIOM_FILE = "axiomFile";

    private final String tacletName;
    private ProofAggregate proofObligation;
    private Throwable ex;

    // The following may all possibly be null
    private String definitionFile;
    private String tacletFile;
    private String[] axiomFiles;
    private String baseDir;

    /**
     * This filter is used to filter out precisely that taclet which has the required name.
     */
    private final TacletFilter filter = new TacletFilter() {
        @Override
        public ImmutableSet<Taclet> filter(List<TacletInfo> taclets) {
            Name name = new Name(tacletName);
            for (TacletInfo tacletInfo : taclets) {
                if (tacletInfo.getTaclet().name().equals(name)) {
                    return DefaultImmutableSet.<Taclet>nil().add(tacletInfo.getTaclet());
                }
            }
            return DefaultImmutableSet.nil();
        }
    };

    /**
     * This listener communicates with the PO loader.
     */
    private final LoaderListener listener = new LoaderListener() {

        @Override
        public void stopped(Throwable exception) {
            LOGGER.error("Exception while loading proof obligation for taclet:", exception);
            ex = exception;
        }

        @Override
        public void stopped(@Nullable ProofAggregate p, ImmutableSet<Taclet> taclets,
                boolean addAsAxioms) {
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
     * @param tacletName the name of the taclet which is to be created
     * @param initConfig the initconfig under which the PO is to be examined
     */
    public TacletProofObligationInput(String tacletName, InitConfig initConfig) {
        this.tacletName = tacletName;
        this.environmentConfig = initConfig;
    }

    /*
     * Fill in only the necessary info.
     */
    @Override
    public Configuration createLoaderConfig() throws IOException {
        var c = new Configuration();
        c.set(IPersistablePO.PROPERTY_CLASS, getClass().getCanonicalName());
        c.set(IPersistablePO.PROPERTY_NAME, name());

        // TODO MU ----- make the file names relative
        // MiscTools.makeFilenamesRelative. However ... I need the store save name ...

        if (tacletFile != null) {
            c.set("tacletFile", tacletFile);
        }
        if (definitionFile != null) {
            c.set("definitionFile", definitionFile);
        }
        if (axiomFiles != null) {
            for (int i = 0; i < axiomFiles.length; i++) {
                String name = AXIOM_FILE + (i == 0 ? "" : (i + 1));
                c.set(name, axiomFiles[i]);
            }
        }
        return c;
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
        TacletLoader loader;

        if (tacletFile == null) {
            // prove a KeY taclet
            loader = new TacletLoader.KeYsTacletsLoader(null, null, environmentConfig.getProfile());
        } else {
            final ProblemInitializer problemInitializer =
                new ProblemInitializer(environmentConfig.getProfile());
            // bugfix: All files are loaded relative to the basedir of the loaded file
            loader = new TacletLoader.TacletFromFileLoader(null, null, problemInitializer,
                new File(baseDir, tacletFile), fileCollection(axiomFiles), environmentConfig);
        }

        ProofEnvironment proofEnv = createProofEnvironment();
        InitConfig initConfig = proofEnv.getInitConfigForEnvironment();

        TacletSoundnessPOLoader poloader =
            new TacletSoundnessPOLoader(listener, filter, true, loader, initConfig, true);

        poloader.startSynchronously();
        if (proofObligation == null) {
            throw new ProofInputException("Cannot instantiate the proof obligation for taclet '"
                + tacletName + "'. Is it defined (in the specified tacletFile?)", ex);
        }
    }

    private ProofEnvironment createProofEnvironment() {
        return new ProofEnvironment(environmentConfig);
    }


    private Collection<File> fileCollection(String[] strings) {
        ArrayList<File> result = new ArrayList<>();
        for (String string : strings) {
            result.add(new File(baseDir, string));
        }
        return result;
    }

    /*
     * just deliver the precalculated PO
     */
    @Override
    public ProofAggregate getPO() throws ProofInputException {
        assert proofObligation != null : "readProblem should have been called first";
        return proofObligation;
    }

    @Override
    public boolean implies(ProofOblInput po) {
        return this == po;
    }

    public static LoadedPOContainer loadFrom(InitConfig initConfig, Properties properties) {
        String tacletName = properties.getProperty(PROPERTY_NAME);
        // This string is parsed by "proveRules.pl"
        if (java.awt.GraphicsEnvironment.isHeadless()) {
            LOGGER.info("Proof obligation for taclet: {}", tacletName);
        }
        TacletProofObligationInput proofOblInput =
            new TacletProofObligationInput(tacletName, initConfig);
        proofOblInput.setLoadInfo(properties);
        return new LoadedPOContainer(proofOblInput);
    }

    private void setLoadInfo(Properties properties) {
        this.baseDir =
            new File(properties.getProperty(IPersistablePO.PROPERTY_FILENAME)).getParent();
        this.tacletFile = properties.getProperty("tacletFile");
        this.definitionFile = properties.getProperty("definitionFile");
        List<String> axioms = new ArrayList<>();
        String name = AXIOM_FILE;
        String axFile = properties.getProperty(name);
        while (axFile != null) {
            axioms.add(axFile);
            name = AXIOM_FILE + (axioms.size() + 1);
            axFile = properties.getProperty(name);
        }
        this.axiomFiles = axioms.toArray(new String[0]);
    }

    public void setLoadInfo(File tacletFile, File definitionFile, Collection<File> axiomFiles) {
        this.tacletFile = tacletFile.toString();
        this.definitionFile = definitionFile.toString();
        this.axiomFiles = new String[axiomFiles.size()];

        int i = 0;
        for (File file : axiomFiles) {
            this.axiomFiles[i] = file.toString();
            i++;
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public KeYJavaType getContainerType() {
        return null;
    }
}
