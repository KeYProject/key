package de.uka.ilkd.key.taclettranslation;

import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.TreeSet;
import java.util.Vector;

import javax.swing.SwingUtilities;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.proof.CompoundProof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.SingleProof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.KeYUserProblemFile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.mgt.AxiomJustification;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletBuilder;
import de.uka.ilkd.key.taclettranslation.lemma.ProofObligationCreator;
import de.uka.ilkd.key.taclettranslation.lemma.TacletLoader;

public class TacletSoundnessPOLoader {

        private final boolean loadAsLemmata;
        private final boolean onlyForProving;

        private LinkedList<LoaderListener> listeners = new LinkedList<LoaderListener>();
        private ProofAggregate resultingProof;
        private ImmutableSet<Taclet> resultingTaclets = DefaultImmutableSet
                        .nil();
 
    
        private final TacletLoader       tacletLoader;
        private TacletFilter tacletFilter;

        static public interface LoaderListener {
                public void started();

                public void stopped(ProofAggregate p,
                                ImmutableSet<Taclet> taclets, boolean addAsAxioms);

                public void stopped(Throwable exception);

                public void progressStarted(Object sender);

                public void reportStatus(Object sender,String string);

                public void resetStatus(Object sender);
        }

        static public interface TacletFilter {
                public ImmutableSet<Taclet> filter(List<TacletInfo> taclets);
        }
        
   

        static public class TacletInfo {
                private Taclet taclet;
                private boolean alreadyInUse;
                private boolean notSupported;

                public Taclet getTaclet() {
                        return taclet;
                }

                public boolean isAlreadyInUse() {
                        return alreadyInUse;
                }

                public boolean isNotSupported() {
                        return notSupported;
                }

                public TacletInfo(Taclet taclet, boolean alreadyInUse,
                                boolean notSupported) {
                        super();
                        this.taclet = taclet;
                        this.alreadyInUse = alreadyInUse;
                        this.notSupported = notSupported;
                }

        }



        public TacletSoundnessPOLoader(
                       
                        LoaderListener listener,
                        TacletFilter filter,
                        boolean loadAsLemmata,
                        TacletLoader loader,
                        boolean onlyForProving) {
                super();
                this.tacletLoader = loader;
                this.tacletFilter = filter;
                this.loadAsLemmata = loadAsLemmata;
                this.onlyForProving = onlyForProving;
       

                if (listener != null) {
                        listeners.add(listener);
                }
        }

        public void addListener(LoaderListener listener) {
                listeners.add(listener);
        }

        public void removeListener(LoaderListener listener) {
                listeners.remove(listener);
        }

        public void start() {
                for (LoaderListener listener : listeners) {
                        listener.started();
                }
                Thread thread = new Thread(new Working());
                thread.start();
        }

        private class Working implements Runnable {
                @Override
                public void run() {
                        try {
                                doWork();
                        } catch (final Throwable exception) {
                                SwingUtilities.invokeLater(new Runnable() {
                                        @Override
                                        public void run() {
                                                for (LoaderListener listener : listeners) {
                                                        listener.stopped(exception);
                                                }
                                        }
                                });
                        } finally {
                                SwingUtilities.invokeLater(new Runnable() {
                                        @Override
                                        public void run() {

                                                for (LoaderListener listener : listeners) {
                                                        listener.stopped(
                                                                        resultingProof,
                                                                        getResultingTaclets(),!loadAsLemmata);
                                                }
                                        }
                                });
                        }
                }
        }

        private Vector<TacletInfo> createTacletInfo(
                        ImmutableSet<Taclet> taclets, ImmutableSet<Taclet> base) {
                Vector<TacletInfo> collectionOfTacletInfo = new Vector<TacletInfo>();
                TreeSet<Taclet> treeSet = new TreeSet<Taclet>(
                                new Comparator<Taclet>() {
                                        @Override
                                        public int compare(Taclet o1, Taclet o2) {
                                                return o1.name()
                                                                .toString()
                                                                .compareTo(o2.name()
                                                                                .toString());
                                        }
                                });
                for (Taclet taclet : base) {
                        treeSet.add(taclet);
                }

                for (Taclet taclet : taclets) {
                        collectionOfTacletInfo
                                        .add(new TacletInfo(taclet, treeSet
                                                        .contains(taclet),
                                                        check(taclet)));
                }
                return collectionOfTacletInfo;
        }

        private boolean check(Taclet taclet) {
                return !(taclet instanceof FindTaclet);
        }


        private void doWork() throws ProofInputException {
      
 
                // Axioms can only be loaded when the taclets are loaded as lemmata.
                ImmutableSet<Taclet> axioms = tacletLoader.loadAxioms();
    
                ImmutableSet<Taclet> taclets = tacletLoader.loadTaclets();
        

                Vector<TacletInfo> collectionOfTacletInfo = createTacletInfo(
                                taclets, getAlreadyInUseTaclets());

                
                resultingTaclets = tacletFilter.filter(collectionOfTacletInfo);

                if (getResultingTaclets().isEmpty()) {
                        return;
                }

                resultingProof = loadAsLemmata ? createProof(tacletLoader.getProofEnvForTaclets(), getResultingTaclets(),
                                tacletLoader.getTacletFile(), axioms) : null;

        }

        private ImmutableSet<Taclet> getAlreadyInUseTaclets() {
                return tacletLoader.getTacletsAlreadyInUse();
        }

        private ProofAggregate createProof(ProofEnvironment proofEnvForTaclets,
                        ImmutableSet<Taclet> taclets,
                        KeYUserProblemFile keyFile, ImmutableSet<Taclet> axioms) {
                removeTaclets(proofEnvForTaclets.getInitConfig(),taclets);
                ProofObligationCreator creator = new ProofObligationCreator();
                ProofAggregate p = creator.create(taclets,
                                proofEnvForTaclets.getInitConfig(), axioms,
                                listeners);
                
                proofEnvForTaclets.registerRules(taclets,
                                AxiomJustification.INSTANCE);
                
                if(onlyForProving){
                        for(Taclet taclet : proofEnvForTaclets.getInitConfig().getTaclets()){
                                proofEnvForTaclets.getJustifInfo().addJustification(taclet, AxiomJustification.INSTANCE); 
                        }
                }
                
                registerProofs(p, proofEnvForTaclets, keyFile);
                return p;
        }
        
        private void removeTaclets(InitConfig initConfig, ImmutableSet<Taclet> taclets){
                ImmutableSet<Taclet> oldTaclets = initConfig.getTaclets();
                ImmutableSet<Taclet> newTaclets = DefaultImmutableSet.nil();
                HashMap<Taclet,TacletBuilder> map = initConfig.getTaclet2Builder();
                for(Taclet taclet: oldTaclets){
                        if(!taclets.contains(taclet)){
                                newTaclets = newTaclets.add(taclet);
                        }else{
                                map.remove(taclet);
                        }
                }
                initConfig.setTaclets(newTaclets);
        }

        public void registerProofs(ProofAggregate aggregate,
                        ProofEnvironment proofEnv, ProofOblInput keyFile) {
                if (aggregate instanceof CompoundProof) {
                        CompoundProof cp = (CompoundProof) aggregate;
                        for (ProofAggregate child : cp.getChildren()) {
                                registerProofs(child, proofEnv, keyFile);
                        }
                } else {
                      assert aggregate instanceof SingleProof;
                        proofEnv.registerProof(keyFile, aggregate);
               }
        }

        public ProofAggregate getResultingProof() {
                return resultingProof;
        }

        public ImmutableSet<Taclet> getResultingTaclets() {
                return resultingTaclets;
        }

}
