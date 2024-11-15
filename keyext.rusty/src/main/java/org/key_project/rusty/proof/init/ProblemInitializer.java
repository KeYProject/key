/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof.init;


import java.io.IOException;
import java.util.*;

import org.key_project.logic.Namespace;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.rusty.Services;
import org.key_project.rusty.proof.ProofAggregate;
import org.key_project.rusty.proof.io.*;
import org.key_project.rusty.proof.io.consistency.FileRepo;
import org.key_project.util.collection.DefaultImmutableSet;
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

        // read Java
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

    // TODO
    private void readRust(EnvInput envInput, InitConfig initConfig) throws ProofInputException {
        /*
         * // this method must only be called once per init config
         * assert !initConfig.getServices().getJavaInfo().rec2key().parsedSpecial();
         * assert initConfig.getServices().getJavaModel() == null;
         *
         * // read Java source and classpath settings
         * envInput.setInitConfig(initConfig);
         * final String javaPath = envInput.readJavaPath();
         * final List<File> classPath = envInput.readClassPath();
         * final File bootClassPath;
         * bootClassPath = envInput.readBootClassPath();
         *
         * final Includes includes = envInput.readIncludes();
         *
         * if (fileRepo != null) {
         * // set the paths in the FileRepo (all three methods can deal with null parameters)
         * fileRepo.setJavaPath(javaPath);
         * fileRepo.setClassPath(classPath);
         * fileRepo.setBootClassPath(bootClassPath);
         * }
         *
         * // weigl: 2021-01, Early including the includes of the KeYUserProblemFile,
         * // this allows to use included symbols inside JML.
         * for (var fileName : includes.getRuleSets()) {
         * KeYFile keyFile = new KeYFile(fileName.file().getName(), fileName, progMon,
         * envInput.getProfile(), fileRepo);
         * readEnvInput(keyFile, initConfig);
         * }
         *
         * // create Recoder2KeY, set classpath
         * final Recoder2KeY r2k = new Recoder2KeY(initConfig.getServices(),
         * initConfig.namespaces());
         * r2k.setClassPath(bootClassPath, classPath);
         *
         * // read Java (at least the library classes)
         * if (javaPath != null) {
         * reportStatus("Reading Java source");
         * final ProjectSettings settings = initConfig.getServices().getJavaInfo()
         * .getKeYProgModelInfo().getServConf().getProjectSettings();
         * final PathList searchPathList = settings.getSearchPathList();
         * if (searchPathList.find(javaPath) == null) {
         * searchPathList.add(javaPath);
         * }
         * Collection<String> var = getClasses(javaPath);
         * if (envInput.isIgnoreOtherJavaFiles()) {
         * String file = envInput.getJavaFile();
         * if (var.contains(file)) {
         * var = Collections.singletonList(file);
         * }
         * }
         * // support for single file loading
         * final String[] cus = var.toArray(new String[0]);
         * try {
         * r2k.readCompilationUnitsAsFiles(cus, fileRepo);
         * } catch (ParseExceptionInFile e) {
         * throw new ProofInputException(e);
         * }
         * } else {
         * reportStatus("Reading Java libraries");
         * r2k.parseSpecialClasses(fileRepo);
         * }
         * File initialFile = envInput.getInitialFile();
         * initConfig.getServices().setJavaModel(
         * JavaModel.createJavaModel(javaPath, classPath, bootClassPath, includes, initialFile));
         */
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
            // setUpProofHelper(po, pa);

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
