/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.taclettranslation.lemma;

import java.io.File;
import java.util.Collection;
import java.util.HashMap;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProblemInitializer.ProblemInitializerListener;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.KeYFile;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.tacletbuilder.TacletBuilder;
import de.uka.ilkd.key.util.ProgressMonitor;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

public abstract class TacletLoader {

    protected final ProgressMonitor monitor;
    protected final ProblemInitializerListener listener;
    protected final Profile profile;
    protected ProofEnvironment proofEnvironment;

    public TacletLoader(ProgressMonitor monitor, ProblemInitializerListener listener,
            Profile profile) {
        super();
        this.monitor = monitor;
        this.listener = listener;
        this.profile = profile;
    }

    /**
     * get the set of axioms from the axiom files if applicable.
     */
    public abstract ImmutableSet<Taclet> loadAxioms() throws ProofInputException;

    /**
     * get the set of taclets to examine (either from the system or from a file)
     */
    public abstract ImmutableList<Taclet> loadTaclets() throws ProofInputException;

    /**
     * get the taclet base which is considered fix (?)
     */
    public abstract ImmutableSet<Taclet> getTacletsAlreadyInUse();

    /**
     * subclasses give a special proof obligation input per proof. They can choose the implementing
     * class and pass to it any necessary information.
     */
    public abstract ProofOblInput getTacletFile(Proof proof);

    /**
     * When proving existing system taclets, all rules which occurred AFTER to the desired taclet
     * need to be eliminated from the set of available taclets to avoid circular proofs.
     *
     * This method removes all taclets in initConfig's taclet database from given first taclet.
     *
     * Taclets are stored in ImmutableSets which fortunately enough still have a fixed order due to
     * their implementation using immutable lists.
     *
     * @param taclet the taclet for which PO will be generated. Remove all taclets after this
     *        taclet.
     *
     * @param initConfig the initial config from which the taclet to prove and all following taclets
     *        have been removed.
     */

    public void manageAvailableTaclets(InitConfig initConfig, Taclet tacletToProve) {
        ImmutableList<Taclet> sysTaclets = initConfig.getTaclets();

        ImmutableList<Taclet> newTaclets = ImmutableSLList.nil();
        HashMap<Taclet, TacletBuilder<? extends Taclet>> map = initConfig.getTaclet2Builder();
        boolean tacletfound = false;
        for (Taclet taclet : sysTaclets) {
            if (taclet.equals(tacletToProve)) {
                tacletfound = true;
            }

            if (!tacletfound) {
                newTaclets = newTaclets.prepend(taclet);
            } else {
                map.remove(taclet);
            }
        }

        initConfig.setTaclets(newTaclets.reverse());
    }

    public ProofEnvironment getProofEnvForTaclets() {
        if (proofEnvironment == null) {
            EmptyEnvInput envInput = new EmptyEnvInput(profile);
            ProblemInitializer pi =
                new ProblemInitializer(monitor, new Services(profile), listener);

            try {
                proofEnvironment = new ProofEnvironment(pi.prepare(envInput));
            } catch (ProofInputException e) {
                throw new RuntimeException(e);
            }
        }
        return proofEnvironment;
    }

    public static class TacletFromFileLoader extends TacletLoader {
        private InitConfig initConfig;
        private final File fileForTaclets;
        private final Collection<File> filesForAxioms;
        private final ProblemInitializer problemInitializer;

        public TacletFromFileLoader(ProgressMonitor pm, ProblemInitializerListener listener,
                ProblemInitializer problemInitializer, File fileForTaclets,
                Collection<File> filesForAxioms, InitConfig initConfig) {
            super(pm, listener, initConfig.getProfile());
            this.fileForTaclets = fileForTaclets;
            this.filesForAxioms = filesForAxioms;
            this.problemInitializer = problemInitializer;
            this.initConfig = initConfig;
        }

        public TacletFromFileLoader(ProgressMonitor pm, ProblemInitializerListener listener,
                ProblemInitializer problemInitializer, Profile profile, File fileForTaclets,
                Collection<File> filesForAxioms) {
            super(pm, listener, profile);
            this.fileForTaclets = fileForTaclets;
            this.filesForAxioms = filesForAxioms;
            this.problemInitializer = problemInitializer;
        }

        public TacletFromFileLoader(TacletFromFileLoader loader, InitConfig initConfig) {
            this(loader.monitor, loader.listener, makeProblemInitializer(loader, initConfig),
                loader.profile, loader.fileForTaclets, loader.filesForAxioms);
            assert initConfig == null || loader.profile == initConfig.getProfile();
            this.initConfig = initConfig;
        }

        private static ProblemInitializer makeProblemInitializer(TacletFromFileLoader loader,
                InitConfig initConfig) {
            return new ProblemInitializer(loader.monitor, initConfig.getServices(),
                loader.listener);
        }

        private void prepareKeYFile(File file) throws ProofInputException {
            KeYFile keyFileDefs = new KeYFile(file.getName(), file, monitor, profile);
            if (initConfig != null) {
                problemInitializer.readEnvInput(keyFileDefs, initConfig);
            } else {
                initConfig = problemInitializer.prepare(keyFileDefs);
            }
        }

        @Override
        public ImmutableList<Taclet> loadTaclets() throws ProofInputException {

            // No axioms file:
            if (initConfig == null) {
                initConfig = getProofEnvForTaclets().getInitConfigForEnvironment();
            }

            int sizeBefore = initConfig.getTaclets().size();

            prepareKeYFile(fileForTaclets);

            ImmutableList<Taclet> listAfter = initConfig.getTaclets();

            return listAfter.take(sizeBefore);
        }

        @Override
        public ImmutableSet<Taclet> loadAxioms() throws ProofInputException {
            ImmutableSet<Taclet> axioms = DefaultImmutableSet.nil();
            for (File f : filesForAxioms) {
                prepareKeYFile(f);
            }

            return axioms;
        }


        @Override
        public ProofOblInput getTacletFile(Proof proof) {
            String name = proof.name().toString();
            assert name.startsWith("Taclet: ")
                    : "This depends (unfortunately) on the name of the proof";
            TacletProofObligationInput result =
                new TacletProofObligationInput(name.substring(8), null);
            result.setLoadInfo(fileForTaclets, new File("unknown"), filesForAxioms);
            return result;
        }

        @Override
        public ImmutableSet<Taclet> getTacletsAlreadyInUse() {
            return DefaultImmutableSet.nil();
        }

    }

    public static class KeYsTacletsLoader extends TacletLoader {

        public KeYsTacletsLoader(ProgressMonitor monitor, ProblemInitializerListener listener,
                Profile profile) {
            super(monitor, listener, profile);
        }

        @Override
        public ImmutableSet<Taclet> loadAxioms() {
            return DefaultImmutableSet.nil();
        }

        @Override
        public ImmutableList<Taclet> loadTaclets() {
            return getProofEnvForTaclets().getInitConfigForEnvironment().getTaclets();
        }

        @Override
        public ProofOblInput getTacletFile(Proof proof) {
            String name = proof.name().toString();
            assert name.startsWith("Taclet: ")
                    : "This depends (unfortunately) on the name of the proof";
            return new TacletProofObligationInput(name.substring(8), null);
        }


        @Override
        public ImmutableSet<Taclet> getTacletsAlreadyInUse() {
            return DefaultImmutableSet.nil();
        }
    }
}
