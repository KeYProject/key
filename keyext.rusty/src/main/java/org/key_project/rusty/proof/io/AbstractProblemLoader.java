/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof.io;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.nio.file.*;
import java.util.Comparator;
import java.util.LinkedList;
import java.util.List;
import java.util.ServiceLoader;
import java.util.function.Consumer;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import java.util.zip.ZipFile;

import org.key_project.rusty.Services;
import org.key_project.rusty.proof.Node;
import org.key_project.rusty.proof.Proof;
import org.key_project.rusty.proof.ProofAggregate;
import org.key_project.rusty.proof.init.*;
import org.key_project.rusty.proof.init.IPersistablePO.LoadedPOContainer;
import org.key_project.rusty.proof.init.loader.ProofObligationLoader;
import org.key_project.rusty.proof.io.consistency.FileRepo;
import org.key_project.rusty.proof.io.consistency.SimpleFileRepo;
import org.key_project.rusty.settings.Configuration;
import org.key_project.rusty.speclang.SLEnvInput;
import org.key_project.util.java.IOUtil;

public abstract class AbstractProblemLoader {
    /**
     * The file or folder to load.
     */
    private final File file;

    /**
     * The filename of the proof in the zipped file (null if file is not a proof bundle).
     */
    private File proofFilename;

    /**
     * The global includes to use.
     */
    private final List<File> includes;

    /**
     * The {@link ProblemLoaderControl} to use.
     */
    private final ProblemLoaderControl control;

    /**
     * The {@link Profile} to use for new {@link Proof}s.
     */
    private final Profile profileOfNewProofs;

    /**
     * The instantiated {@link EnvInput} which describes the file to load.
     */
    private EnvInput envInput;

    /**
     * The instantiated {@link ProblemInitializer} used during the loading process.
     */
    private ProblemInitializer problemInitializer;

    /**
     * The instantiated {@link InitConfig} which provides access to the loaded source elements and
     * specifications.
     */
    private InitConfig initConfig;

    /**
     * The instantiate proof or {@code null} if no proof was instantiated during loading process.
     */
    private Proof proof;

    /**
     * The {@link ReplayResult} if available or {@code null} otherwise.
     */
    private ReplayResult result;

    /**
     * Whether warnings (generated when loading the proof) should be ignored
     * and not shown to the user.
     */
    private boolean ignoreWarnings = false;

    /**
     * Constructor.
     *
     * @param file The file or folder to load.
     * @param includes Optional includes to consider.
     * @param profileOfNewProofs The {@link Profile} to use for new {@link Proof}s.
     * @param control The {@link ProblemLoaderControl} to use.
     *        {@link ProblemLoaderControl#selectProofObligation(InitConfig)} if no {@link Proof} is
     *        defined by the loaded proof or {@code false} otherwise which still allows to work with
     *        the loaded {@link InitConfig}.
     */
    protected AbstractProblemLoader(File file,
            List<File> includes, Profile profileOfNewProofs,
            ProblemLoaderControl control) {
        this.file = file;
        this.control = control;
        this.profileOfNewProofs =
            profileOfNewProofs != null ? profileOfNewProofs : RustProfile.getDefaultInstance();
        this.includes = includes;
    }

    protected void setProof(Proof proof) {
        this.proof = proof;
    }

    /**
     * Executes the loading process and tries to instantiate a proof and to re-apply rules on it if
     * possible.
     *
     * @throws ProofInputException Occurred Exception.
     * @throws IOException Occurred Exception.
     * @throws ProblemLoaderException Occurred Exception.
     */
    public final void load() throws Exception {
        load(null);
    }

    /**
     * Executes the loading process and tries to instantiate a proof and to re-apply rules on it if
     * possible.
     *
     * @param callbackProofLoaded optional callback, called when the proof is loaded but not yet
     *        replayed
     * @throws ProofInputException Occurred Exception.
     * @throws IOException Occurred Exception.
     * @throws ProblemLoaderException Occurred Exception.
     */
    public final void load(Consumer<Proof> callbackProofLoaded)
            throws Exception {
        // control.loadingStarted(this);

        loadEnvironment();

        LoadedPOContainer poContainer = createProofObligationContainer();
        ProofAggregate proofList = null;
        try {
            if (poContainer == null) {
                // if (askUiToSelectAProofObligationIfNotDefinedByLoadedFile) {
                // selectAndLoadProof(control, initConfig);
                // }
            } else {
                proofList = createProof(poContainer);
                loadSelectedProof(poContainer, proofList, callbackProofLoaded);
            }
        } finally {
            // control.loadingFinished(this, poContainer, proofList, result);
        }
    }

    /**
     * Loads and initialized the proof environment.
     *
     * @throws ProofInputException Occurred Exception.
     * @throws IOException Occurred Exception.
     * @see AbstractProblemLoader#load()
     */
    protected void loadEnvironment() throws ProofInputException, IOException {
        FileRepo fileRepo = createFileRepo();

        var timeBeforeEnv = System.nanoTime();
        // LOGGER.info("Loading environment from " + file);
        envInput = createEnvInput(fileRepo);
        // LOGGER.debug(
        // "Environment load took " + PerfScope.formatTime(System.nanoTime() - timeBeforeEnv));
        problemInitializer = createProblemInitializer(fileRepo);
        var beforeInitConfig = System.nanoTime();
        // LOGGER.info("Creating init config");
        initConfig = createInitConfig();
        initConfig.setFileRepo(fileRepo);
        // LOGGER.debug(
        // "Init config took " + PerfScope.formatTime(System.nanoTime() - beforeInitConfig));
        // if (!problemInitializer.getWarnings().isEmpty() && !ignoreWarnings) {
        // control.reportWarnings(problemInitializer.getWarnings());
        // }
    }

    /**
     * Loads a proof from the proof list.
     *
     * @param poContainer the container created by {@link #createProofObligationContainer()}.
     * @param proofList the proof list containing the proof to load.
     * @param callbackProofLoaded optional callback, called before the proof is replayed
     * @see AbstractProblemLoader#load()
     */
    protected void loadSelectedProof(LoadedPOContainer poContainer, ProofAggregate proofList,
            Consumer<Proof> callbackProofLoaded) {
        // try to replay first proof
        proof = proofList.getProof(poContainer.getProofNum());

        if (proof != null) {
            if (callbackProofLoaded != null) {
                callbackProofLoaded.accept(proof);
            }
            // OneStepSimplifier.refreshOSS(proof);
            result = replayProof(proof);
            // LOGGER.info("Replay result: {}", result.getStatus());
        }
    }

    /**
     * Find first 'non-wrapper' exception type in cause chain.
     */
    private Throwable unwrap(Throwable e) {
        while (e instanceof ProblemLoaderException) {
            e = e.getCause();
        }
        return e;
    }

    /**
     * Creates a new FileRepo (with or without consistency) based on the settings.
     *
     * @return a FileRepo that can be used for proof bundle saving
     * @throws IOException if for some reason the FileRepo can not be created (e.g. temporary
     *         directory can not be created).
     */
    protected FileRepo createFileRepo() throws IOException {
        // create a FileRepo depending on the settings
        /*
         * TODO:boolean consistent = ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings()
         * .isEnsureSourceConsistency();
         *
         * if (consistent) {
         * return new DiskFileRepo("KeYTmpFileRepo");
         * } else {
         * return new SimpleFileRepo();
         * }
         */
        return new SimpleFileRepo();
    }

    /**
     * Instantiates the {@link EnvInput} which represents the file to load.
     *
     * @param fileRepo the FileRepo used to ensure consistency between proof and source code
     * @return The created {@link EnvInput}.
     * @throws IOException Occurred Exception.
     */
    protected EnvInput createEnvInput(FileRepo fileRepo) throws IOException {

        final String filename = file.getName();

        // set the root directory of the FileRepo (used for resolving paths)
        fileRepo.setBaseDir(file.toPath());

        if (filename.endsWith(".rs")) {
            // rust file, probably enriched by specifications
            SLEnvInput ret = null;
            if (file.getParentFile() == null) {
                ret = new SLEnvInput(".", profileOfNewProofs, includes);
            } else {
                ret = new SLEnvInput(file.getParentFile().getAbsolutePath(), profileOfNewProofs,
                    includes);
            }
            ret.setRustFile(file.getAbsolutePath());
            return ret;
        } else if (filename.endsWith(".zproof")) { // zipped proof package
            /*
             * TODO: Currently it is not possible to load proof bundles with multiple proofs. This
             * feature is still pending, since the functionality to save multiple proofs in one
             * (consistent!) package is not yet implemented (see ProofManagement tool from 1st
             * HacKeYthon). The current implementation allows the user to pick one of the proofs via
             * a dialog. The user choice is given to the AbstractProblem Loader via the proofName
             * field.
             */
            if (proofFilename == null) { // no proof to load given -> try to determine one
                // create a list of all *.proof files (only top level in bundle)
                List<Path> proofs;
                try (ZipFile bundle = new ZipFile(file)) {
                    proofs = bundle.stream().filter(e -> !e.isDirectory())
                            .filter(e -> e.getName().endsWith(".proof"))
                            .map(e -> Paths.get(e.getName())).collect(Collectors.toList());
                }
                if (!proofs.isEmpty()) {
                    // load first proof found in file
                    proofFilename = proofs.get(0).toFile();
                } else {
                    // no proof found in bundle!
                    throw new IOException("The bundle contains no proof to load!");
                }
            }

            // we are sure proofFilename is set now:
            // assert proofFilename != null;

            // unzip to a temporary directory
            Path tmpDir = Files.createTempDirectory("KeYunzip");
            IOUtil.extractZip(file.toPath(), tmpDir);

            // hook for deleting tmpDir + content at program exit
            Runtime.getRuntime().addShutdownHook(new Thread(() -> {
                try (Stream<Path> s = Files.walk(tmpDir)) {
                    // delete the temporary directory with all contained files
                    s.sorted(Comparator.reverseOrder()).map(Path::toFile)
                            .forEach(File::delete);
                } catch (IOException e) {
                    // this is called at program exist, so we only print a console message
                    // LOGGER.warn("Failed to clean up temp dir", e);
                }
            }));

            // point the FileRepo to the temporary directory
            fileRepo.setBaseDir(tmpDir);

            // create new KeYUserProblemFile pointing to the (unzipped) proof file
            PathMatcher matcher = FileSystems.getDefault().getPathMatcher("glob:**.proof");

            // construct the absolute path to the unzipped proof file
            Path unzippedProof = tmpDir.resolve(proofFilename.toPath());

            return new KeYUserProblemFile(unzippedProof.toString(), unzippedProof.toFile(),
                fileRepo, profileOfNewProofs, false);
        } else if (filename.endsWith(".key") || filename.endsWith(".proof")
                || filename.endsWith(".proof.gz")) {
            // KeY problem specification or saved proof
            return new KeYUserProblemFile(filename, file, fileRepo, profileOfNewProofs,
                filename.endsWith(".proof.gz"));
        } else if (file.isDirectory()) {
            // directory containing java sources, probably enriched
            // by specifications
            return new SLEnvInput(file.getPath(), profileOfNewProofs,
                includes);
        } else {
            if (filename.lastIndexOf('.') != -1) {
                throw new IllegalArgumentException("Unsupported file extension '"
                    + filename.substring(filename.lastIndexOf('.')) + "' of read-in file "
                    + filename + ". Allowed extensions are: .key, .proof, .rs or "
                    + "complete directories.");
            } else {
                throw new FileNotFoundException(
                    "File or directory\n\t " + filename + "\n not found.");
            }
        }
    }

    /**
     * Instantiates the {@link ProblemInitializer} to use.
     *
     * @param fileRepo the FileRepo used to ensure consistency between proof and source code
     * @return The {@link ProblemInitializer} to use.
     */
    protected ProblemInitializer createProblemInitializer(FileRepo fileRepo) {
        Profile profile = envInput.getProfile();
        ProblemInitializer pi = new ProblemInitializer(new Services(profile));
        pi.setFileRepo(fileRepo);
        return pi;
    }

    /**
     * Creates the {@link InitConfig}.
     *
     * @return The created {@link InitConfig}.
     * @throws ProofInputException Occurred Exception.
     */
    protected InitConfig createInitConfig() throws ProofInputException {
        return problemInitializer.prepare(envInput);
    }

    /**
     * Creates a {@link LoadedPOContainer} if available which contains the {@link ProofOblInput} for
     * which a {@link Proof} should be instantiated.
     *
     * @return The {@link LoadedPOContainer} or {@code null} if not available.
     * @throws IOException Occurred Exception.
     */
    protected LoadedPOContainer createProofObligationContainer() throws Exception {
        final String chooseContract;
        final Configuration proofObligation;

        if (envInput instanceof KeYFile keyFile) {
            chooseContract = keyFile.chooseContract();
            proofObligation = keyFile.getProofObligation();
        } else {
            chooseContract = null;
            proofObligation = null;
        }

        // Instantiate proof obligation
        if (envInput instanceof ProofOblInput && chooseContract == null
                && proofObligation == null) {
            return new LoadedPOContainer((ProofOblInput) envInput);
        } /*
           * else if (chooseContract != null && !chooseContract.isEmpty()) {
           * return loadByChosenContract(chooseContract);
           * }
           */ else if (proofObligation != null) {
            return loadByProofObligation(proofObligation);
        } else {
            return null;
        }
    }

    /**
     * Creates a {@link Proof} for the given {@link LoadedPOContainer} and tries to apply rules
     * again.
     *
     * @param poContainer The {@link LoadedPOContainer} to instantiate a {@link Proof} for.
     * @return The instantiated {@link Proof}.
     * @throws ProofInputException Occurred Exception.
     */
    protected ProofAggregate createProof(LoadedPOContainer poContainer) throws ProofInputException {
        ProofAggregate proofList =
            problemInitializer.startProver(initConfig, poContainer.getProofOblInput());

        for (Proof p : proofList.getProofs()) {
            // register proof
            /*
             * initConfig.getServices().getSpecificationRepository()
             * .registerProof(poContainer.getProofOblInput(), p);
             * initConfig.getFileRepo().registerProof(p);
             */
        }

        return proofList;
    }

    private LoadedPOContainer loadByProofObligation(Configuration proofObligation)
            throws Exception {
        // Load proof obligation settings
        proofObligation.set("#key.filename", file.getAbsolutePath());

        /*
         * if (poPropertiesToForce != null) {
         * proofObligation.overwriteWith(proofObligation);
         * }
         */

        String poClass = proofObligation.getString("class");
        if (poClass == null || poClass.isEmpty()) {
            throw new IOException("Proof obligation class property \""
                + "class" + "\" is not defined or empty.");
        }
        ServiceLoader<ProofObligationLoader> loader =
            ServiceLoader.load(ProofObligationLoader.class);
        for (ProofObligationLoader poloader : loader) {
            if (poloader.handles(poClass)) {
                return poloader.loadFrom(initConfig, proofObligation);
            }
        }
        throw new IllegalArgumentException(
            "There is no builder that can build the PO for the id " + poClass);
    }

    private ReplayResult replayProof(Proof proof) {
        // TODO: rework, when we load rust files
        List<Throwable> errors = new LinkedList<>();
        String status = "";

        Node lastTouchedNode = proof.root();

        IntermediatePresentationProofFileParser parser =
            new IntermediatePresentationProofFileParser(proof);
        IntermediatePresentationProofFileParser.Result parserResult = null;
        IntermediateProofReplayer replayer = null;
        IntermediateProofReplayer.Result replayResult = null;
        ReplayResult result;
        try {
            assert envInput instanceof KeYUserProblemFile;
            problemInitializer.tryReadProof(parser, (KeYUserProblemFile) envInput);
            parserResult = parser.getResult();

            replayer = new IntermediateProofReplayer(this, proof, parserResult);
            replayResult =
                replayer.replay();
            lastTouchedNode = replayResult.getLastSelectedGoal() != null
                    ? replayResult.getLastSelectedGoal().getNode()
                    : proof.root();
        } catch (ProofInputException e) {
            if (parserResult == null || parserResult.errors() == null
                    || parserResult.errors().isEmpty() || replayer == null
                    || replayResult == null || replayResult.getErrors() == null
                    || replayResult.getErrors().isEmpty()) {
                // this exception was something unexpected
                errors.add(e);
            }
        } finally {
            if (parserResult != null) {
                status = parserResult.status();
                errors.addAll(parserResult.errors());
            }
            status += (status.isEmpty() ? "Proof replayed successfully." : "\n\n")
                    + (replayResult != null ? replayResult.getStatus()
                            : "Error while loading proof.");
            if (replayResult != null) {
                errors.addAll(replayResult.getErrors());
            }
            result = new ReplayResult(status, errors, lastTouchedNode);
        }

        return result;
    }

    /**
     * Returns the file or folder to load.
     *
     * @return The file or folder to load.
     */
    public File getFile() {
        return file;
    }

    /**
     * Returns the instantiated {@link EnvInput} which describes the file to load.
     *
     * @return The instantiated {@link EnvInput} which describes the file to load.
     */
    public EnvInput getEnvInput() {
        return envInput;
    }

    /**
     * Returns the instantiated {@link InitConfig} which provides access to the loaded source
     * elements and specifications.
     *
     * @return The instantiated {@link InitConfig} which provides access to the loaded source
     *         elements and specifications.
     */
    public InitConfig getInitConfig() {
        return initConfig;
    }

    /**
     * Returns the instantiate proof or {@code null} if no proof was instantiated during loading
     * process.
     *
     * @return The instantiate proof or {@code null} if no proof was instantiated during loading
     *         process.
     */
    public Proof getProof() {
        return proof;
    }

    /**
     * Returns the {@link ReplayResult} if available.
     *
     * @return The {@link ReplayResult} or {@code null} if not available.
     */
    public ReplayResult getResult() {
        return result;
    }

    public static class ReplayResult {
        private final Node node;
        private final List<Throwable> errors;
        private final String status;

        public ReplayResult(String status, List<Throwable> errors, Node node) {
            this.status = status;
            this.errors = errors;
            this.node = node;
        }

        public Node getNode() {
            return node;
        }

        public String getStatus() {
            return status;
        }

        public List<Throwable> getErrorList() {
            return errors;
        }

        public boolean hasErrors() {
            return errors != null && !errors.isEmpty();
        }
    }
}
