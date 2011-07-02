package de.uka.ilkd.key.taclettranslation;

import java.io.File;
import java.util.Collection;
import java.util.Comparator;
import java.util.LinkedList;
import java.util.TreeSet;
import java.util.Vector;

import javax.swing.SwingUtilities;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.CompoundProof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.SingleProof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.KeYUserProblemFile;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProblemInitializer.ProblemInitializerListener;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.mgt.AxiomJustification;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.taclettranslation.lemma.ProofObligationCreator;
import de.uka.ilkd.key.taclettranslation.lemma.TacletLoader;
import de.uka.ilkd.key.util.KeYRecoderExcHandler;
import de.uka.ilkd.key.util.ProgressMonitor;

public class TacletSoundnessPOLoader {
        private final ProgressMonitor progressMonitor;
        private final File file;
        private final Collection<File> filesForAxioms = new LinkedList<File>();
        private final File fileForDefinitions;
        private final boolean loadAsLemmata;

        private ProofEnvironment env;
        private LinkedList<LoaderListener> listeners = new LinkedList<LoaderListener>();
        private ProofAggregate resultingProof;
        private ImmutableSet<Taclet> resultingTaclets = DefaultImmutableSet
                        .nil();
        private final ProblemInitializer problemInitializer;
        private final ProblemInitializerListener piListener;
        private TacletFilter tacletFilter;

        static public interface LoaderListener {
                public void started();

                public void stopped(ProofAggregate p,
                                ImmutableSet<Taclet> taclets, boolean addAsAxioms);

                public void stopped(Throwable exception);
        }

        static public interface TacletFilter {
                public ImmutableSet<Taclet> filter(Vector<TacletInfo> taclets);
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

        public TacletSoundnessPOLoader(ProgressMonitor progressMonitor,
                        File file, ProofEnvironment referenceEnv,
                        LoaderListener listener,
                        ProblemInitializerListener piListener,
                        TacletFilter filter,boolean loadAsLemmata) {
                this(progressMonitor, file, referenceEnv, listener, piListener,
                                filter, null, file,loadAsLemmata);
        }

        public TacletSoundnessPOLoader(ProgressMonitor progressMonitor,
                        File file, ProofEnvironment referenceEnv,
                        LoaderListener listener,
                        ProblemInitializerListener piListener,
                        TacletFilter filter, Collection<File> filesForAxioms,
                        File fileForDefinitions, boolean loadAsLemmata) {
                super();
                this.progressMonitor = progressMonitor;
                this.file = file;
                this.env = referenceEnv;
                this.tacletFilter = filter;
                this.fileForDefinitions = fileForDefinitions == null ? file
                                : fileForDefinitions;
                this.loadAsLemmata = loadAsLemmata;

                if (filesForAxioms != null) {
                        this.filesForAxioms.addAll(filesForAxioms);
                }
                problemInitializer = new ProblemInitializer(progressMonitor,
                                env.getInitConfig().getProfile(), new Services(
                                                new KeYRecoderExcHandler()),
                                false, piListener);
                this.piListener = piListener;

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

        private ImmutableSet<Taclet> readAxioms(Collection<File> files,
                        InitConfig initConfig, ProgressMonitor pm,
                        ProblemInitializer pi,
                        ProofEnvironment proofEnvForTaclets)
                        throws ProofInputException {
                ImmutableSet<Taclet> axioms = DefaultImmutableSet.nil();
                for (File f : files) {
                        KeYUserProblemFile keyFile = new KeYUserProblemFile(
                                        f.getName(), f, pm);
                        ImmutableSet<Taclet> taclets = TacletLoader.INSTANCE
                                        .load(keyFile, initConfig);
                        proofEnvForTaclets.registerRules(taclets,
                                        AxiomJustification.INSTANCE);
                        axioms = axioms.union(taclets);
                }

                return axioms;
        }

        private void doWork() throws ProofInputException {
      
                KeYUserProblemFile keyFile = new KeYUserProblemFile(
                                file.getName(), file, progressMonitor);
                InitConfig initConfig;

                KeYUserProblemFile keyFileDefs = new KeYUserProblemFile(
                                "Definitions", fileForDefinitions,
                                progressMonitor);

                initConfig = problemInitializer.prepare(keyFileDefs);

                keyFileDefs.close();
                
                ImmutableSet<Taclet> emptySet = DefaultImmutableSet.nil();
                // Axioms can only be loaded when the taclets are loaded as lemmata.
                ImmutableSet<Taclet> axioms = loadAsLemmata ? readAxioms(filesForAxioms,
                                initConfig, progressMonitor,
                                problemInitializer, env) :  emptySet;

                ImmutableSet<Taclet> taclets = TacletLoader.INSTANCE.load(
                                keyFile, initConfig);

                Vector<TacletInfo> collectionOfTacletInfo = createTacletInfo(
                                taclets, getAlreadyInUseTaclets());

                if (piListener != null) {
                        piListener.resetStatus(problemInitializer);
                }

                resultingTaclets = tacletFilter.filter(collectionOfTacletInfo);

                if (getResultingTaclets().isEmpty()) {
                        return;
                }

                resultingProof = loadAsLemmata ? createProof(env, getResultingTaclets(),
                                keyFile, axioms) : null;

        }

        private ImmutableSet<Taclet> getAlreadyInUseTaclets() {
                return env.getInitConfig().getTaclets();
        }

        private ProofAggregate createProof(ProofEnvironment proofEnvForTaclets,
                        ImmutableSet<Taclet> taclets,
                        KeYUserProblemFile keyFile, ImmutableSet<Taclet> axioms) {
                ProofObligationCreator creator = new ProofObligationCreator();
                ProofAggregate p = creator.create(taclets,
                                proofEnvForTaclets.getInitConfig(), axioms,
                                piListener);
                proofEnvForTaclets.registerRules(taclets,
                                AxiomJustification.INSTANCE);

                registerProofs(p, proofEnvForTaclets, keyFile);
                return p;
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
