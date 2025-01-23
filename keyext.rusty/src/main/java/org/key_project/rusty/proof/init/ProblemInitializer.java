/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof.init;


import java.io.File;
import java.io.IOException;
import java.nio.file.Path;
import java.util.LinkedHashSet;
import java.util.Set;

import org.key_project.logic.Namespace;
import org.key_project.logic.Term;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.HirConverter;
import org.key_project.rusty.ast.HirRustyReader;
import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.logic.NamespaceSet;
import org.key_project.rusty.logic.op.ElementaryUpdate;
import org.key_project.rusty.logic.op.Modality;
import org.key_project.rusty.logic.op.ProgramVariable;
import org.key_project.rusty.proof.Goal;
import org.key_project.rusty.proof.Proof;
import org.key_project.rusty.proof.ProofAggregate;
import org.key_project.rusty.proof.RustModel;
import org.key_project.rusty.proof.io.*;
import org.key_project.rusty.proof.io.consistency.FileRepo;
import org.key_project.rusty.proof.mgt.AxiomJustification;
import org.key_project.rusty.rule.BuiltInRule;
import org.key_project.rusty.rule.Rule;
import org.key_project.rusty.util.MiscTools;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.NonNull;


public final class ProblemInitializer {
    private static InitConfig baseConfig;
    private final Services services;

    private final Set<EnvInput> alreadyParsed = new LinkedHashSet<>();
    /**
     * the FileRepo responsible for consistency between source code and proofs
     */
    private FileRepo fileRepo;
    private ImmutableSet<String> warnings = DefaultImmutableSet.nil();

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    public ProblemInitializer(Services services) {
        this.services = services;
    }

    public ProblemInitializer(Profile profile) {
        if (profile == null) {
            throw new IllegalArgumentException("Given profile is null");
        }

        this.services = new Services(profile);
    }

    // --------------------------------------------------------------------------
    // internal methods
    // --------------------------------------------------------------------------


    public void setFileRepo(FileRepo fileRepo) {
        this.fileRepo = fileRepo;
    }

    public InitConfig prepare(EnvInput envInput) throws ProofInputException {
        InitConfig currentBaseConfig = baseConfig != null ? baseConfig.copy() : null;

        alreadyParsed.clear();

        // the first time, read in standard rules
        Profile profile = services.getProfile();
        if (currentBaseConfig == null || profile != currentBaseConfig.getProfile()) {
            currentBaseConfig = new InitConfig(services);
            RuleSource tacletBase = profile.getStandardRules().getTacletBase();
            if (tacletBase != null) {
                KeYFile tacletBaseFile = new KeYFile("taclet base",
                    profile.getStandardRules().getTacletBase(), profile);
                readEnvInput(tacletBaseFile, currentBaseConfig);
            }
            // remove traces of the generic sorts within the base configuration
            cleanupNamespaces(currentBaseConfig);
            baseConfig = currentBaseConfig;
        }

        return prepare(envInput, currentBaseConfig);
    }

    private InitConfig prepare(EnvInput envInput, InitConfig referenceConfig)
            throws ProofInputException {
        // create initConfig
        // InitConfig initConfig = referenceConfig.copy();
        InitConfig initConfig = referenceConfig.copy();

        // configureTermLabelSupport(initConfig);

        // read Rust
        readRust(envInput, initConfig);

        // register function and predicate symbols defined by Java program
        final var rustInfo = initConfig.getServices().getRustInfo();
        final Namespace<@NonNull Function> functions =
            initConfig.getServices().getNamespaces().functions();
        if (rustInfo != null) {
            // TODO: Declare fields (how?)
            for (var fn : rustInfo.getAllFunctions()) {
                functions.add(fn);
            }
        } else {
            throw new ProofInputException("Problem initialization without JavaInfo!");
        }

        // read envInput
        readEnvInput(envInput, initConfig);

        // remove generic sorts defined in KeY file
        cleanupNamespaces(initConfig);

        // done
        return initConfig;
    }

    private void readRust(EnvInput envInput, InitConfig initConfig) throws ProofInputException {
        // this method must only be called once per init config
        // assert !initConfig.getServices().getRustInfo().rec2key().parsedSpecial();
        assert initConfig.getServices().getRustModel() == null;

        // read Rust source
        envInput.setInitConfig(initConfig);
        final String rustPath = envInput.readRustPath();

        final Includes includes = envInput.readIncludes();

        if (fileRepo != null) {
            // set the paths in the FileRepo
            fileRepo.setRustyPath(rustPath);
        }

        for (var fileName : includes.getRuleSets()) {
            KeYFile keyFile = new KeYFile(fileName.file().getName(), fileName,
                envInput.getProfile(), fileRepo);
            readEnvInput(keyFile, initConfig);
        }
        if (rustPath != null) {
            try {
                var output =
                    HirRustyReader.getWrapperOutput(Path.of(rustPath).toAbsolutePath().normalize());
                var converter = new HirConverter(initConfig.getServices(), output.specs());
                converter.convertCrate(output.crate());
            } catch (IOException e) {
                throw new ProofInputException(e);
            }
        }
        File initialFile = envInput.getInitialFile();
        initConfig.getServices().setRustModel(
            RustModel.create(rustPath, includes, initialFile));
    }

    public void readEnvInput(EnvInput envInput, InitConfig initConfig) throws ProofInputException {
        if (alreadyParsed.add(envInput)) {
            // read includes
            if (!(envInput instanceof LDTInput)) {
                readIncludes(envInput, initConfig);
            }

            // read envInput itself
            envInput.setInitConfig(initConfig);
            warnings = warnings.union(envInput.read());

            // reset the variables namespace
            initConfig.namespaces().setVariables(new Namespace<>());
        }
    }

    /**
     * Helper for readEnvInput().
     */
    private void readIncludes(EnvInput envInput, InitConfig initConfig) throws ProofInputException {
        envInput.setInitConfig(initConfig);

        Includes in = envInput.readIncludes();

        // read LDT includes
        readLDTIncludes(in, initConfig);

        // read normal includes
        for (String fileName : in.getIncludes()) {
            KeYFile keyFile =
                new KeYFile(fileName, in.get(fileName), envInput.getProfile(), fileRepo);
            readEnvInput(keyFile, initConfig);
        }
    }

    /**
     * Helper for readIncludes().
     */
    private void readLDTIncludes(Includes in, InitConfig initConfig) throws ProofInputException {
        // avoid infinite recursion
        if (in.getLDTIncludes().isEmpty()) {
            return;
        }

        // collect all ldt includes into a single LDTInput
        KeYFile[] keyFiles = new KeYFile[in.getLDTIncludes().size()];

        int i = 0;

        for (String name : in.getLDTIncludes()) {
            keyFiles[i] =
                new KeYFile(name, in.get(name), initConfig.getProfile(), fileRepo);
            i++;
        }

        LDTInput ldtInp = new LDTInput(keyFiles, initConfig.getProfile());

        // read the LDTInput
        readEnvInput(ldtInp, initConfig);
    }

    // Why does it say here that it removes schema variables when it just removes variables?
    // And with symbols are only functions meant?

    /**
     * Removes all schema variables, all generic sorts and all sort-depending symbols for a generic
     * sort out of the namespaces. Helper for readEnvInput().
     * <p>
     * See bug report #1185, #1189 (in Mantis)
     */
    private void cleanupNamespaces(InitConfig initConfig) {
        var newVarNS = new Namespace<@NonNull QuantifiableVariable>();
        // TODO: cover generics once they are added
        /*
         * Namespace<Sort> newSortNS = new Namespace<>();
         * Namespace<Function> newFuncNS = new Namespace<>();
         * for (Sort n : initConfig.sortNS().allElements()) {
         * if (!(n instanceof GenericSort)) {
         * newSortNS.addSafely(n);
         * }
         * }
         * for (Function n : initConfig.funcNS().allElements()) {
         * if (!(n instanceof SortDependingFunction
         * && ((SortDependingFunction) n).getSortDependingOn() instanceof GenericSort)) {
         * newFuncNS.addSafely(n);
         * }
         * }
         * initConfig.getServices().getNamespaces().setSorts(newSortNS);
         * initConfig.getServices().getNamespaces().setFunctions(newFuncNS);
         */
        initConfig.getServices().getNamespaces().setVariables(newVarNS);
    }

    public ProofAggregate startProver(InitConfig initConfig, ProofOblInput po)
            throws ProofInputException {
        // progressStarted(this);
        try {
            // read problem
            // reportStatus("Loading problem \"" + po.name() + "\"");
            po.readProblem();
            ProofAggregate pa = po.getPO();
            // final work
            setUpProofHelper(pa);

            /*
             * if (Debug.ENABLE_DEBUG) {
             * print(pa.getFirstProof());
             * }
             */

            // done
            // proofCreated(pa);
            return pa;
        } catch (ProofInputException e) {
            // reportException(po, e);
            throw e;
        } finally {
            // progressStopped(this);
        }
    }

    private void setUpProofHelper(ProofAggregate pl) throws ProofInputException {
        if (pl == null) {
            throw new ProofInputException("No proof");
        }

        // register non-built-in rules
        Proof[] proofs = pl.getProofs();
        for (int i = 0; i < proofs.length; i++) {
            proofs[i].getInitConfig().registerRules(proofs[i].getInitConfig().getTaclets(),
                AxiomJustification.INSTANCE);
            // setProgress(3 + i * proofs.length);
            // register built in rules
            Profile profile = proofs[i].getInitConfig().getProfile();
            final ImmutableList<BuiltInRule> rules =
                profile.getStandardRules().standardBuiltInRules();
            int j = 0;
            final int step = rules.size() != 0 ? (7 / rules.size()) : 0;
            for (Rule r : rules) {
                proofs[i].getInitConfig().registerRule(r, profile.getJustification(r));
                // setProgress((++j) * step + 3 + i * proofs.length);
            }
            // if (step == 0) {
            // setProgress(10 + i * proofs.length);
            // }

            // TODO: refactor Proof.setNamespaces() so this becomes unnecessary
            proofs[i].setNamespaces(proofs[i].getNamespaces());
            populateNamespaces(proofs[i]);
        }
    }

    /**
     * Ensures that the passed proof's namespaces contain all functions and program variables used
     * in its root sequent.
     */
    private void populateNamespaces(Proof proof) {
        final NamespaceSet namespaces = proof.getNamespaces();
        final Goal rootGoal = proof.openGoals().head();
        for (SequentFormula cf : proof.root().sequent()) {
            populateNamespaces(cf.formula(), namespaces, rootGoal);
        }
    }

    private void populateNamespaces(Term term, NamespaceSet namespaces, Goal rootGoal) {
        for (int i = 0; i < term.arity(); i++) {
            populateNamespaces(term.sub(i), namespaces, rootGoal);
        }

        if (term.op() instanceof Function f) {
            namespaces.functions().add(f);
        } else if (term.op() instanceof ProgramVariable pv) {
            if (namespaces.programVariables().lookup(pv.name()) == null) {
                rootGoal.addProgramVariable((ProgramVariable) term.op());
            }
        } else if (term.op() instanceof ElementaryUpdate eu) {
            final ProgramVariable pv = (ProgramVariable) eu.lhs();
            if (namespaces.programVariables().lookup(pv.name()) == null) {
                rootGoal.addProgramVariable(pv);
            }
        } else if (term.op() instanceof Modality mod) {
            final RustyProgramElement pe = mod.program().program();
            final Services serv = rootGoal.proof().getServices();
            final ImmutableSet<ProgramVariable> freeProgVars =
                MiscTools.getLocalIns(pe, serv).union(MiscTools.getLocalOuts(pe, serv));
            for (ProgramVariable pv : freeProgVars) {
                if (namespaces.programVariables().lookup(pv.name()) == null) {
                    rootGoal.addProgramVariable(pv);
                }
            }
        }
    }

    // TODO see how and when a prover is started
    public ProofAggregate startProver(KeYUserProblemFile file) {
        return null;
    }

    public void tryReadProof(IProofFileParser pfp, KeYUserProblemFile kupf)
            throws ProofInputException {
        // reportStatus("Loading proof", kupf.getNumberOfChars());
        try {
            kupf.readProof(pfp);
            // setProgress(kupf.getNumberOfChars() / 2);
        } catch (IOException e) {
            throw new ProofInputException(e);
        } finally {
            kupf.close();
            // setProgress(kupf.getNumberOfChars());
        }
    }
}
