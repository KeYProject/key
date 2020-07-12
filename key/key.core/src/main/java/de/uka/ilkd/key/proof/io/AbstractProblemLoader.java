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

package de.uka.ilkd.key.proof.io;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.lang.reflect.Method;
import java.net.MalformedURLException;
import java.net.URL;
import java.nio.file.*;
import java.util.*;
import java.util.stream.Collectors;
import java.util.zip.ZipFile;

import org.antlr.runtime.MismatchedTokenException;
import org.key_project.util.java.IOUtil;
import org.key_project.util.reflection.ClassLoaderUtil;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.parser.KeYLexer;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.init.FunctionalOperationContractPO;
import de.uka.ilkd.key.proof.init.IPersistablePO;
import de.uka.ilkd.key.proof.init.IPersistablePO.LoadedPOContainer;
import de.uka.ilkd.key.proof.io.consistency.DiskFileRepo;
import de.uka.ilkd.key.proof.io.consistency.SimpleFileRepo;
import de.uka.ilkd.key.proof.io.consistency.FileRepo;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.KeYUserProblemFile;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.SLEnvInput;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.ExceptionHandlerException;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Triple;

/**
 * <p>
 * This class provides the basic functionality to load something in KeY.
 * The loading process is done in the current {@link Thread} and
 * no user interaction is required.
 * </p>
 * <p>
 * The basic usage of this class is to instantiate a new 
 * {@link SingleThreadProblemLoader} or {@link ProblemLoader}
 * instance which should load the file configured by the constructor's arguments.
 * The next step is to call {@link #load()} which does the loading process and
 * tries to instantiate a proof and to apply rules again if possible. The result
 * of the loading process is available via the getter methods.
 * </p>
 * @author Martin Hentschel
 */
public abstract class AbstractProblemLoader {
    public static class ReplayResult {

		private Node node;
		private List<Throwable> errors;
		private String status;

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

	/**
     * The file or folder to load.
     */
    private final File file;

    /**
     * The filename of the proof in the zipped file (null if file is not a proof bundle).
     */
    private File proofFilename;

    /**
     * The optional class path entries to use.
     */
    private final List<File> classPath;

    /**
     * An optional boot class path.
     */
    private final File bootClassPath;
    
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
     * {@code true} to call {@link UserInterfaceControl#selectProofObligation(InitConfig)}
     * if no {@link Proof} is defined by the loaded proof or 
     * {@code false} otherwise which still allows to work with the loaded {@link InitConfig}.
     */
    private final boolean askUiToSelectAProofObligationIfNotDefinedByLoadedFile;

    /**
     * Some optional additional {@link Properties} for the PO.
     */
    private final Properties poPropertiesToForce;

    /**
     * {@code} true {@link #profileOfNewProofs} will be used as {@link Profile} of new proofs, {@code false} {@link Profile} specified by problem file will be used for new proofs.
     */
    private final boolean forceNewProfileOfNewProofs;
    
    /**
     * The instantiated {@link EnvInput} which describes the file to load.
     */
    private EnvInput envInput;

    /**
     * The instantiated {@link ProblemInitializer} used during the loading process.
     */
    private ProblemInitializer problemInitializer;

    /**
     * The instantiated {@link InitConfig} which provides access to the loaded source elements and specifications.
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
     * Maps internal error codes of the parser to human readable strings.
     * The integers refer to the common MismatchedTokenExceptions,
     * where one token is expected and another is found.
     * Both are usually only referred to by their internal code.
     */
    private final static Map<Pair<Integer,Integer>,String> mismatchErrors;
    private final static Map<Integer,String> missedErrors;
    
    static {
        // format: (expected, found)
        mismatchErrors = new HashMap<Pair<Integer, Integer>, String>();
        mismatchErrors.put(new Pair<Integer, Integer>(KeYLexer.SEMI, KeYLexer.COMMA), "there may be only one declaration per line");
        
        missedErrors = new HashMap<Integer, String>();
        missedErrors.put(KeYLexer.RPAREN, "closing parenthesis");
        missedErrors.put(KeYLexer.RBRACE, "closing brace");
        missedErrors.put(KeYLexer.SEMI, "semicolon");
    }

    /**
     * Constructor.
     * @param file The file or folder to load.
     * @param classPath The optional class path entries to use.
     * @param bootClassPath An optional boot class path.
     * @param includes Optional includes to consider.
     * @param profileOfNewProofs The {@link Profile} to use for new {@link Proof}s.
     * @param forceNewProfileOfNewProofs {@code} true {@link #profileOfNewProofs} will be used as {@link Profile} of new proofs, {@code false} {@link Profile} specified by problem file will be used for new proofs.
     * @param control The {@link ProblemLoaderControl} to use.
     * @param askUiToSelectAProofObligationIfNotDefinedByLoadedFile {@code true} to call {@link UserInterfaceControl#selectProofObligation(InitConfig)} if no {@link Proof} is defined by the loaded proof or {@code false} otherwise which still allows to work with the loaded {@link InitConfig}.
     */
    public AbstractProblemLoader(File file, 
                                 List<File> classPath, 
                                 File bootClassPath,
                                 List<File> includes,
                                 Profile profileOfNewProofs, 
                                 boolean forceNewProfileOfNewProofs,
                                 ProblemLoaderControl control,
                                 boolean askUiToSelectAProofObligationIfNotDefinedByLoadedFile,
                                 Properties poPropertiesToForce) {
        this.file = file;
        this.classPath = classPath;
        this.bootClassPath = bootClassPath;
        this.control = control;
        this.profileOfNewProofs = profileOfNewProofs != null ? profileOfNewProofs : AbstractProfile.getDefaultProfile();
        this.forceNewProfileOfNewProofs = forceNewProfileOfNewProofs;
        this.askUiToSelectAProofObligationIfNotDefinedByLoadedFile = askUiToSelectAProofObligationIfNotDefinedByLoadedFile;
        this.poPropertiesToForce = poPropertiesToForce;
        this.includes = includes;
    }

    /**
     * Executes the loading process and tries to instantiate a proof
     * and to re-apply rules on it if possible.
     * @throws ProofInputException Occurred Exception.
     * @throws IOException Occurred Exception.
     * @throws ProblemLoaderException Occurred Exception.
     */
    public void load() throws ProofInputException, IOException, ProblemLoaderException {
        control.loadingStarted(this);

        FileRepo fileRepo = createFileRepo();

        // Read environment
        envInput = createEnvInput(fileRepo);
        problemInitializer = createProblemInitializer(fileRepo);
        initConfig = createInitConfig();
        initConfig.setFileRepo(fileRepo);
        if (!problemInitializer.getWarnings().isEmpty()) {
            control.reportWarnings(problemInitializer.getWarnings());
        }
        // Read proof obligation settings
        LoadedPOContainer poContainer = createProofObligationContainer();
        ProofAggregate proofList = null;
        try {
            if (poContainer == null) {
                if (askUiToSelectAProofObligationIfNotDefinedByLoadedFile) {
                    if (control.selectProofObligation(initConfig)) {
                        return;
                    } else {
                        // That message would be reported otherwise. Undesired.
                        // return new ProblemLoaderException(this, "Aborted.");
                        return;
                    }
                } else {
                    // Do not instantiate any proof but allow the user of the DefaultProblemLoader
                    // to access the loaded InitConfig.
                    return;
                }
            }

            // Create and register proof at specification repository
            proofList = createProof(poContainer);

            // try to replay first proof
            proof = proofList.getProof(poContainer.getProofNum());


            if (proof != null) {
                OneStepSimplifier.refreshOSS(proof);
                result = replayProof(proof);
            }

            // this message is propagated to the top level in console mode
            return; // Everything fine
        } catch (Throwable t) {
            // Throw this exception; otherwise, it can for instance occur
            // that "result" will be null (if replayProof(...) fails) and
            // we get a NullPointerException that is hard to analyze.
            throw t;
        } finally {
            control.loadingFinished(this, poContainer, proofList, result);
        }
    }

    /**
     * Find first 'non-wrapper' exception type in cause chain.
     */
    private Throwable unwrap(Throwable e) {
        while (e instanceof ExceptionHandlerException
               || e instanceof ProblemLoaderException)
            e = e.getCause();
        return e;
    }

    /**
     * Tries to recover parser errors and make them human-readable,
     * rewrap them into ProblemLoaderExceptions.
     */
    protected ProblemLoaderException recoverParserErrorMessage(Exception e) {
        // try to resolve error message
        final Throwable c0 = unwrap(e);
        if (c0 instanceof org.antlr.runtime.RecognitionException) {
            final org.antlr.runtime.RecognitionException re = (org.antlr.runtime.RecognitionException) c0;
            final org.antlr.runtime.Token occurrence = re.token; // may be null
            if (c0 instanceof org.antlr.runtime.MismatchedTokenException) {
                if (c0 instanceof org.antlr.runtime.MissingTokenException) {
                    final org.antlr.runtime.MissingTokenException mte = (org.antlr.runtime.MissingTokenException) c0;
                    // TODO: other commonly missed tokens
                    final String readable = missedErrors.get(mte.expecting);
                    final String token = readable==null? "token id "+mte.expecting: readable;
                    final String msg = "Syntax error: missing "+token+
                                    (occurrence == null? "": " at "+occurrence.getText())
                                    +" statement ("+mte.input.getSourceName()
                                    +":"+mte.line+")";
                    return new ProblemLoaderException(this, msg, mte);
                    // TODO other ANTLR exceptions
                } else {
                    final org.antlr.runtime.MismatchedTokenException mte = (MismatchedTokenException) c0;
                    final String genericMsg = "expected "+mte.expecting
                                    +", but found "+mte.c;
                    final String readable = mismatchErrors.get(new Pair<Integer, Integer>(mte.expecting,mte.c));
                    final String msg = "Syntax error: " 
                                    +(readable == null? genericMsg: readable)
                                    +" ("+mte.input.getSourceName()
                                    +":"+mte.line+")";
                    return new ProblemLoaderException(this, msg, mte);
                } 
            }
        }
        // default
        return new ProblemLoaderException(this, "Loading proof input failed", e);
    }

    /**
     * Creates a new FileRepo (with or without consistency) based on the settings.
     * @return a FileRepo that can be used for proof bundle saving
     * @throws IOException if for some reason the FileRepo can not be created
     *   (e.g. temporary directory can not be created).
     */
    protected FileRepo createFileRepo() throws IOException {
        // create a FileRepo depending on the settings
        boolean consistent = ProofIndependentSettings.DEFAULT_INSTANCE
                                                     .getGeneralSettings()
                                                     .isEnsureSourceConsistency();

        if (consistent) {
            return new DiskFileRepo("KeYTmpFileRepo");
        } else {
            return new SimpleFileRepo();
        }
    }

    /**
     * Instantiates the {@link EnvInput} which represents the file to load.
     * @param fileRepo the FileRepo used to ensure consistency between proof and source code
     * @return The created {@link EnvInput}.
     * @throws IOException Occurred Exception.
     */
    protected EnvInput createEnvInput(FileRepo fileRepo) throws IOException {

        final String filename = file.getName();

        // set the root directory of the FileRepo (used for resolving paths)
        fileRepo.setBaseDir(file.toPath());

        if (filename.endsWith(".java")) {
            // java file, probably enriched by specifications
            if (file.getParentFile() == null) {
                return new SLEnvInput(".", classPath, bootClassPath, profileOfNewProofs, includes);
            } else {
                return new SLEnvInput(file.getParentFile().getAbsolutePath(),
                                classPath, bootClassPath, profileOfNewProofs, includes);
            }
        } else if (filename.endsWith(".zproof")) {            // zipped proof package
            /* TODO: Currently it is not possible to load proof bundles with multiple proofs.
             *  This feature is still pending, since the functionality to save multiple proofs in
             *  one (consistent!) package is not yet implemented (see ProofManagement tool from
             *  1st HacKeYthon).
             *  The current implementation allows the user to pick one of the proofs via a dialog.
             *  The user choice is given to the AbstractProblem Loader via the proofName field.
             */
            if (proofFilename == null) {    // no proof to load given -> try to determine one
                // create a list of all *.proof files (only top level in bundle)
                ZipFile bundle = new ZipFile(file);
                List<Path> proofs = bundle.stream()
                    .filter(e -> !e.isDirectory())
                    .filter(e -> e.getName().endsWith(".proof"))
                    .map(e -> Paths.get(e.getName()))
                    .collect(Collectors.toList());
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
                try {
                    // delete the temporary directory with all contained files
                    Files.walk(tmpDir)
                         .sorted(Comparator.reverseOrder())
                         .map(Path::toFile)
                         .forEach(File::delete);
                } catch (IOException e) {
                    // this is called at program exist, so we only print a console message
                    e.printStackTrace();
                }
            }));

            // point the FileRepo to the temporary directory
            fileRepo.setBaseDir(tmpDir);

            // create new KeYUserProblemFile pointing to the (unzipped) proof file
            PathMatcher matcher = FileSystems.getDefault().getPathMatcher("glob:**.proof");

            // construct the absolute path to the unzipped proof file
            Path unzippedProof = tmpDir.resolve(proofFilename.toPath());

            return new KeYUserProblemFile(unzippedProof.toString(), unzippedProof.toFile(),
                fileRepo, control, profileOfNewProofs, false);
        } else if (filename.endsWith(".key") || filename.endsWith(".proof")
              || filename.endsWith(".proof.gz")) {
            // KeY problem specification or saved proof
            return new KeYUserProblemFile(filename, file, fileRepo, control,
                        profileOfNewProofs, filename.endsWith(".proof.gz"));
        } else if (file.isDirectory()) {
            // directory containing java sources, probably enriched
            // by specifications
            return new SLEnvInput(file.getPath(), classPath, bootClassPath, profileOfNewProofs,
                    includes);
        } else {
            if (filename.lastIndexOf('.') != -1) {
                throw new IllegalArgumentException("Unsupported file extension \'"
                                + filename.substring(filename.lastIndexOf('.'))
                                + "\' of read-in file " + filename
                                + ". Allowed extensions are: .key, .proof, .java or "
                                + "complete directories.");
            } else {
                throw new FileNotFoundException("File or directory\n\t " + filename
                                + "\n not found.");
            }
        }
    }

    /**
     * Instantiates the {@link ProblemInitializer} to use.
     * @param fileRepo the FileRepo used to ensure consistency between proof and source code
     * @param registerProof Register loaded {@link Proof}
     * @return The {@link ProblemInitializer} to use.
     */
    protected ProblemInitializer createProblemInitializer(FileRepo fileRepo) {
        Profile profile = forceNewProfileOfNewProofs ? profileOfNewProofs : envInput.getProfile();
        ProblemInitializer pi = new ProblemInitializer(control, new Services(profile), control);
        pi.setFileRepo(fileRepo);
        return pi;
    }

    /**
     * Creates the {@link InitConfig}.
     * @return The created {@link InitConfig}.
     * @throws ProofInputException Occurred Exception.
     */
    protected InitConfig createInitConfig() throws ProofInputException {
        return problemInitializer.prepare(envInput);
    }

    /**
     * Creates a {@link LoadedPOContainer} if available which contains
     * the {@link ProofOblInput} for which a {@link Proof} should be instantiated.
     * @return The {@link LoadedPOContainer} or {@code null} if not available.
     * @throws IOException Occurred Exception.
     */
    protected LoadedPOContainer createProofObligationContainer() throws IOException {
        final String chooseContract;
        final String proofObligation;
        if (envInput instanceof KeYFile) {
            KeYFile keyFile = (KeYFile)envInput;
            chooseContract = keyFile.chooseContract();
            proofObligation = keyFile.getProofObligation();
        }
        else {
            chooseContract = null;
            proofObligation = null;
        }
        // Instantiate proof obligation
        if (envInput instanceof ProofOblInput && chooseContract == null && proofObligation == null) {
            return new LoadedPOContainer((ProofOblInput)envInput);
        }
        else if (chooseContract != null && chooseContract.length() > 0) {
            int proofNum = 0;
            String baseContractName = null;
            int ind = -1;
            for (String tag : FunctionalOperationContractPO.TRANSACTION_TAGS.values()) {
                ind = chooseContract.indexOf("." + tag);
                if (ind > 0) {
                    break;
                }
                proofNum++;
            }
            if (ind == -1) {
                baseContractName = chooseContract;
                proofNum = 0;
            }
            else {
                baseContractName = chooseContract.substring(0, ind);
            }
            final Contract contract = initConfig.getServices().getSpecificationRepository().getContractByName(baseContractName);
            if (contract == null) {
                throw new RuntimeException("Contract not found: " + baseContractName);
            }
            else {
                return new LoadedPOContainer(contract.createProofObl(initConfig), proofNum);
            }
        }
        else if (proofObligation != null && proofObligation.length() > 0) {
            // Load proof obligation settings
            final Properties properties = new Properties();
            properties.load(new ByteArrayInputStream(proofObligation.getBytes()));
            properties.setProperty(IPersistablePO.PROPERTY_FILENAME, file.getAbsolutePath());
            if (poPropertiesToForce != null) {
                properties.putAll(poPropertiesToForce);
            }
            String poClass = properties.getProperty(IPersistablePO.PROPERTY_CLASS);
            if (poClass == null || poClass.isEmpty()) {
                throw new IOException("Proof obligation class property \"" + IPersistablePO.PROPERTY_CLASS + "\" is not defiend or empty.");
            }
            try {
                // Try to instantiate proof obligation by calling static method: public static LoadedPOContainer loadFrom(InitConfig initConfig, Properties properties) throws IOException
                Class<?> poClassInstance = ClassLoaderUtil.getClassforName(poClass);
                Method loadMethod = poClassInstance.getMethod("loadFrom", InitConfig.class, Properties.class);
                return (LoadedPOContainer)loadMethod.invoke(null, initConfig, properties);
            }
            catch (Exception e) {
                throw new IOException("Can't call static factory method \"loadFrom\" on class \"" + poClass + "\".", e);
            }
        }
        else {
            return null;
        }
    }

    /**
     * Creates a {@link Proof} for the given {@link LoadedPOContainer} and
     * tries to apply rules again.
     * @param poContainer The {@link LoadedPOContainer} to instantiate a {@link Proof} for.
     * @return The instantiated {@link Proof}.
     * @throws ProofInputException Occurred Exception.
     */
    protected ProofAggregate createProof(LoadedPOContainer poContainer) throws ProofInputException {
    	
        ProofAggregate proofList = 
        		problemInitializer.startProver(initConfig, poContainer.getProofOblInput());

        for (Proof p : proofList.getProofs()) {
            // register proof
            initConfig.getServices().getSpecificationRepository()
                                    .registerProof(poContainer.getProofOblInput(), p);
            initConfig.getFileRepo().registerProof(p);
        }

        return proofList;
    }

    /**
     * Run proof script if it is present in the input data.
     *
     * @return <code>true</code> iff there is a proof script to run
     */
    public boolean hasProofScript() {
        if (envInput instanceof KeYUserProblemFile) {
            KeYUserProblemFile kupf = (KeYUserProblemFile) envInput;
            return kupf.hasProofScript();
        }
        return false;
    }

    public Pair<String, Location> readProofScript() throws ProofInputException {
        assert envInput instanceof KeYUserProblemFile;
        KeYUserProblemFile kupf = (KeYUserProblemFile) envInput;

            Triple<String, Integer, Integer> script = kupf.readProofScript();
        URL url = null;
        try {
            url = kupf.getInitialFile().toURI().toURL();
        } catch (MalformedURLException e) {
            throw new ProofInputException(e);
        }
        Location location = new Location(url, script.second, script.third);

        return new Pair<String, Location>(script.first, location);
    }

    public Pair<String, Location> getProofScript() throws ProblemLoaderException {
        if(hasProofScript()) {
            try {
                return readProofScript();
            } catch (ProofInputException e) {
                throw new ProblemLoaderException(this, e);
            }
        } else {
            return null;
        }
    }

    private ReplayResult replayProof(Proof proof) throws ProofInputException, ProblemLoaderException {
        String status = "";
        List<Throwable> errors = new LinkedList<Throwable>();
        Node lastTouchedNode = proof.root();
        
        IProofFileParser parser = null;
        IntermediateProofReplayer replayer = null;
        IntermediatePresentationProofFileParser.Result parserResult = null;
        IntermediateProofReplayer.Result replayResult = null;

        final String ossStatus =
                (String) proof.getSettings().getStrategySettings()
                        .getActiveStrategyProperties()
                        .get(StrategyProperties.OSS_OPTIONS_KEY);
        ReplayResult result;
        try {
        	assert envInput instanceof KeYUserProblemFile;
        	    
                parser = new IntermediatePresentationProofFileParser(proof);
                problemInitializer.tryReadProof(parser, (KeYUserProblemFile) envInput);
                parserResult = ((IntermediatePresentationProofFileParser) parser).getResult();
                
                // Parser is no longer needed, set it to null to free memory.
                parser = null;
                
                // For loading, we generally turn on one step simplification to be
                // able to load proofs that used it even if the user has currently
                // turned OSS off.
                StrategyProperties newProps = proof.getSettings()
                        .getStrategySettings().getActiveStrategyProperties();
                newProps.setProperty(StrategyProperties.OSS_OPTIONS_KEY,
                        StrategyProperties.OSS_ON);
                Strategy.updateStrategySettings(proof, newProps);
                OneStepSimplifier.refreshOSS(proof);
                
                replayer = new IntermediateProofReplayer(this, proof, parserResult);
                replayResult = replayer.replay();
                
                lastTouchedNode = replayResult.getLastSelectedGoal() != null ? replayResult.getLastSelectedGoal().node() : proof.root();

        } catch (Exception e) {
        	if (parserResult == null || parserResult.getErrors() == null || parserResult.getErrors().isEmpty() ||
        	        replayer == null || replayResult == null || replayResult.getErrors() == null || replayResult.getErrors().isEmpty()) {
        		// this exception was something unexpected
        		errors.add(e);
        	}
        } finally {
            if (parserResult != null) {
                status = parserResult.getStatus();
                errors.addAll(parserResult.getErrors());
            }
            status += (status.isEmpty() ? "" : "\n\n") + (replayResult != null ? replayResult.getStatus() : "Error while loading proof.");
            if (replayResult != null) {
                errors.addAll(replayResult.getErrors());
            }
            
            StrategyProperties newProps = 
                proof.getSettings().getStrategySettings()
                        .getActiveStrategyProperties();
            newProps.setProperty(StrategyProperties.OSS_OPTIONS_KEY,
                            ossStatus);
            Strategy.updateStrategySettings(proof, newProps);
            OneStepSimplifier.refreshOSS(proof);
            
            result = new ReplayResult(status, errors, lastTouchedNode);
        }
        	
        
        return result;
    }

    /**
     * Returns the file or folder to load.
     * @return The file or folder to load.
     */
    public File getFile() {
        return file;
    }

    /**
     * Returns the optional class path entries to use.
     * @return The optional class path entries to use.
     */
    public List<File> getClassPath() {
        return classPath;
    }

    /**
     * Returns the optional boot class path.
     * @return The optional boot class path.
     */
    public File getBootClassPath() {
        return bootClassPath;
    }

    /**
     * Returns the instantiated {@link EnvInput} which describes the file to load.
     * @return The instantiated {@link EnvInput} which describes the file to load.
     */
    public EnvInput getEnvInput() {
        return envInput;
    }

    /**
     * Returns the instantiated {@link ProblemInitializer} used during the loading process.
     * @return The instantiated {@link ProblemInitializer} used during the loading process.
     */
    public ProblemInitializer getProblemInitializer() {
        return problemInitializer;
    }

    /**
     * Returns the instantiated {@link InitConfig} which provides access to the loaded source elements and specifications.
     * @return The instantiated {@link InitConfig} which provides access to the loaded source elements and specifications.
     */
    public InitConfig getInitConfig() {
        return initConfig;
    }

    /**
     * Returns the instantiate proof or {@code null} if no proof was instantiated during loading process.
     * @return The instantiate proof or {@code null} if no proof was instantiated during loading process.
     */
    public Proof getProof() {
        return proof;
    }

    /**
     * Returns the {@link ReplayResult} if available.
     * @return The {@link ReplayResult} or {@code null} if not available.
     */
    public ReplayResult getResult() {
       return result;
    }

    public void setProofPath(File proofFilename) {
        this.proofFilename = proofFilename;
    }
}
