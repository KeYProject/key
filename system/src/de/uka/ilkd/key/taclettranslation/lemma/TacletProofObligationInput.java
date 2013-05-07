package de.uka.ilkd.key.taclettranslation.lemma;

import java.io.IOException;
import java.util.List;
import java.util.Properties;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.IPersistablePO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.Profile;
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
    private final Profile profile;

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
            System.out.println(p);
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

    /**
     * Instantiates a new taclet proof obligation input object.
     * 
     * @param tacletName
     *            the name of the taclet which is to be created
     * @param profile
     *            the profile under which the taclet is to be examined
     */
    public TacletProofObligationInput(String tacletName, Profile profile) {
        this.tacletName = tacletName;
        this.profile = profile;
    }

    
    /* 
     * Fill in only the necessary info.
     */
    @Override 
    public void fillSaveProperties(Properties properties) throws IOException {
        properties.setProperty(IPersistablePO.PROPERTY_CLASS, getClass().getCanonicalName());
        properties.setProperty(IPersistablePO.PROPERTY_NAME, name());
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
        TacletLoader loader = new TacletLoader.KeYsTacletsLoader(null, null, profile);

        TacletSoundnessPOLoader poloader = 
                new TacletSoundnessPOLoader(listener, filter, true, loader);

        poloader.startSynchronously();
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
        return new LoadedPOContainer(new TacletProofObligationInput(tacletName, 
                initConfig.getProfile()));
    }
}
