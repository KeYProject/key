/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.init;

import java.io.*;
import java.nio.charset.StandardCharsets;
import java.util.*;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.Field;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.schemajava.SchemaJavaParser;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.JavaModel;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.io.*;
import de.uka.ilkd.key.proof.io.consistency.FileRepo;
import de.uka.ilkd.key.proof.mgt.AxiomJustification;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.ProgressMonitor;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import recoder.io.PathList;
import recoder.io.ProjectSettings;


public final class ProblemInitializer {
    private static final Logger LOGGER = LoggerFactory.getLogger(ProblemInitializer.class);

    private static InitConfig baseConfig;
    private final Services services;
    private final ProgressMonitor progMon;
    private final Set<EnvInput> alreadyParsed = new LinkedHashSet<>();
    private final ProblemInitializerListener listener;
    /**
     * the FileRepo responsible for consistency between source code and proofs
     */
    private FileRepo fileRepo;
    private ImmutableSet<PositionedString> warnings = DefaultImmutableSet.nil();

    public ProblemInitializer(ProgressMonitor mon, Services services,
            ProblemInitializerListener listener) {
        this.services = services;
        this.progMon = mon;
        this.listener = listener;
    }

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    public ProblemInitializer(Profile profile) {
        if (profile == null) {
            throw new IllegalArgumentException("Given profile is null");
        }

        this.progMon = null;
        this.listener = null;
        this.services = new Services(Objects.requireNonNull(profile));
    }

    private void progressStarted(Object sender) {
        if (listener != null) {
            listener.progressStarted(sender);
        }
    }


    // -------------------------------------------------------------------------
    // internal methods
    // -------------------------------------------------------------------------

    private void progressStopped(Object sender) {
        if (listener != null) {
            listener.progressStopped(sender);
        }
    }

    private void proofCreated(ProofAggregate proofAggregate) {
        if (listener != null) {
            listener.proofCreated(this, proofAggregate);
        }
    }

    /**
     * displays the status report in the status line
     */
    private void reportStatus(String status) {
        if (listener != null) {
            listener.resetStatus(this);
            listener.reportStatus(this, status);
        }

    }

    /**
     * displays the status report in the status line and the maximum used by a progress bar
     *
     * @param status the String to be displayed in the status line
     * @param progressMax an int describing what is 100 per cent
     */
    private void reportStatus(String status, int progressMax) {
        if (listener != null) {
            listener.resetStatus(this);
            listener.reportStatus(this, status, progressMax);
        }
    }

    private void reportException(ProofOblInput input, Exception e) {
        if (listener != null) {
            listener.reportException(this, input, e);
        }
    }

    private void setProgress(int progress) {
        if (progMon != null) {
            progMon.setProgress(progress);
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
        KeYFile[] keyFile = new KeYFile[in.getLDTIncludes().size()];

        int i = 0;
        reportStatus("Read LDT Includes", in.getIncludes().size());
        for (String name : in.getLDTIncludes()) {

            keyFile[i] =
                new KeYFile(name, in.get(name), progMon, initConfig.getProfile(), fileRepo);
            i++;
            setProgress(i);
        }

        LDTInput ldtInp = new LDTInput(keyFile, (status, progress) -> {
            ProblemInitializer.this.reportStatus(status);
            ProblemInitializer.this.setProgress(progress);
        }, initConfig.getProfile());

        // read the LDTInput
        readEnvInput(ldtInp, initConfig);
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
        reportStatus("Read Includes", in.getIncludes().size());
        int i = 0;
        for (String fileName : in.getIncludes()) {
            KeYFile keyFile =
                new KeYFile(fileName, in.get(fileName), progMon, envInput.getProfile(), fileRepo);
            readEnvInput(keyFile, initConfig);
            setProgress(++i);
        }
    }

    /**
     * get a vector of Strings containing all .java file names in the cfile directory. Helper for
     * readJava().
     */
    private List<String> getClasses(String f) throws ProofInputException {
        File cfile = new File(f);
        List<String> v = new ArrayList<>();
        if (cfile.isDirectory()) {
            String[] list = cfile.list();
            // mu(2008-jan-28): if the directory is not readable for the current user
            // list is set to null, which results in a NullPointerException.
            if (list != null) {
                for (String s : list) {
                    String fullName = cfile.getPath() + File.separator + s;
                    File n = new File(fullName);
                    if (n.isDirectory()) {
                        v.addAll(getClasses(fullName));
                    } else if (s.endsWith(".java")) {
                        v.add(fullName);
                    }
                }
            }
            return v;
        } else {
            throw new ProofInputException("Java model path " + f + " not found.");
        }

    }


    /**
     * Helper for readEnvInput().
     */
    private void readJava(EnvInput envInput, InitConfig initConfig) throws ProofInputException {
        // this method must only be called once per init config
        assert !initConfig.getServices().getJavaInfo().rec2key().parsedSpecial();
        assert initConfig.getServices().getJavaModel() == null;

        // read Java source and classpath settings
        envInput.setInitConfig(initConfig);
        final String javaPath = envInput.readJavaPath();
        final List<File> classPath = envInput.readClassPath();
        final File bootClassPath;
        try {
            bootClassPath = envInput.readBootClassPath();
        } catch (IOException ioe) {
            throw new ProofInputException(ioe);
        }

        final Includes includes = envInput.readIncludes();

        if (fileRepo != null) {
            // set the paths in the FileRepo (all three methods can deal with null parameters)
            fileRepo.setJavaPath(javaPath);
            fileRepo.setClassPath(classPath);
            fileRepo.setBootClassPath(bootClassPath);
        }

        // weigl: 2021-01, Early including the includes of the KeYUserProblemFile,
        // this allows to use included symbols inside JML.
        for (var fileName : includes.getRuleSets()) {
            KeYFile keyFile = new KeYFile(fileName.file().getName(), fileName, progMon,
                envInput.getProfile(), fileRepo);
            readEnvInput(keyFile, initConfig);
        }

        // create Recoder2KeY, set classpath
        final Recoder2KeY r2k = new Recoder2KeY(initConfig.getServices(), initConfig.namespaces());
        r2k.setClassPath(bootClassPath, classPath);

        // read Java (at least the library classes)
        if (javaPath != null) {
            reportStatus("Reading Java source");
            final ProjectSettings settings = initConfig.getServices().getJavaInfo()
                    .getKeYProgModelInfo().getServConf().getProjectSettings();
            final PathList searchPathList = settings.getSearchPathList();
            if (searchPathList.find(javaPath) == null) {
                searchPathList.add(javaPath);
            }
            Collection<String> var = getClasses(javaPath);
            if (envInput.isIgnoreOtherJavaFiles()) {
                String file = envInput.getJavaFile();
                if (var.contains(file)) {
                    var = Collections.singletonList(file);
                }
            }
            // support for single file loading
            final String[] cus = var.toArray(new String[0]);
            try {
                r2k.readCompilationUnitsAsFiles(cus, fileRepo);
            } catch (ParseExceptionInFile e) {
                throw new ProofInputException(e);
            }
        } else {
            reportStatus("Reading Java libraries");
            r2k.parseSpecialClasses(fileRepo);
        }
        File initialFile = envInput.getInitialFile();
        initConfig.getServices().setJavaModel(
            JavaModel.createJavaModel(javaPath, classPath, bootClassPath, includes, initialFile));
    }

    /**
     * Removes all schema variables, all generic sorts and all sort depending symbols for a generic
     * sort out of the namespaces. Helper for readEnvInput().
     * <p>
     * See bug report #1185, #1189 (in Mantis)
     */
    private void cleanupNamespaces(InitConfig initConfig) {
        Namespace<QuantifiableVariable> newVarNS = new Namespace<>();
        Namespace<Sort> newSortNS = new Namespace<>();
        Namespace<Function> newFuncNS = new Namespace<>();
        for (Sort n : initConfig.sortNS().allElements()) {
            if (!(n instanceof GenericSort)) {
                newSortNS.addSafely(n);
            }
        }
        for (Function n : initConfig.funcNS().allElements()) {
            if (!(n instanceof SortDependingFunction
                    && ((SortDependingFunction) n).getSortDependingOn() instanceof GenericSort)) {
                newFuncNS.addSafely(n);
            }
        }
        initConfig.getServices().getNamespaces().setVariables(newVarNS);
        initConfig.getServices().getNamespaces().setSorts(newSortNS);
        initConfig.getServices().getNamespaces().setFunctions(newFuncNS);
    }

    public void readEnvInput(EnvInput envInput, InitConfig initConfig) throws ProofInputException {
        if (alreadyParsed.add(envInput)) {
            // read includes
            if (!(envInput instanceof LDTInput)) {
                readIncludes(envInput, initConfig);
            }

            // read envInput itself
            reportStatus("Reading " + envInput.name());
            envInput.setInitConfig(initConfig);
            warnings = warnings.union(envInput.read());

            // reset the variables namespace
            initConfig.namespaces().setVariables(new Namespace<>());
        }
    }

    private void populateNamespaces(Term term, NamespaceSet namespaces, Goal rootGoal) {
        for (int i = 0; i < term.arity(); i++) {
            populateNamespaces(term.sub(i), namespaces, rootGoal);
        }

        if (term.op() instanceof Function) {
            namespaces.functions().add((Function) term.op());
        } else if (term.op() instanceof ProgramVariable) {
            final ProgramVariable pv = (ProgramVariable) term.op();
            if (namespaces.programVariables().lookup(pv.name()) == null) {
                rootGoal.addProgramVariable((ProgramVariable) term.op());
            }
        } else if (term.op() instanceof ElementaryUpdate) {
            final ProgramVariable pv = (ProgramVariable) ((ElementaryUpdate) term.op()).lhs();
            if (namespaces.programVariables().lookup(pv.name()) == null) {
                rootGoal.addProgramVariable(pv);
            }
        } else if (term.javaBlock() != null && !term.javaBlock().isEmpty()) {
            final ProgramElement pe = term.javaBlock().program();
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

    // what is the purpose of this method?
    private InitConfig determineEnvironment(ProofOblInput po, InitConfig initConfig)
            throws ProofInputException {
        // TODO: what does this actually do?
        ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().updateChoices(initConfig.choiceNS(),
            false);
        return initConfig;
    }

    private void setUpProofHelper(ProofOblInput problem, ProofAggregate pl)
            throws ProofInputException {
        if (pl == null) {
            throw new ProofInputException("No proof");
        }

        // register non-built-in rules
        Proof[] proofs = pl.getProofs();
        reportStatus("Registering rules", proofs.length * 10);
        for (int i = 0; i < proofs.length; i++) {
            proofs[i].getInitConfig().registerRules(proofs[i].getInitConfig().getTaclets(),
                AxiomJustification.INSTANCE);
            setProgress(3 + i * proofs.length);
            // register built in rules
            Profile profile = proofs[i].getInitConfig().getProfile();
            final ImmutableList<BuiltInRule> rules =
                profile.getStandardRules().getStandardBuiltInRules();
            int j = 0;
            final int step = rules.size() != 0 ? (7 / rules.size()) : 0;
            for (Rule r : rules) {
                proofs[i].getInitConfig().registerRule(r, profile.getJustification(r));
                setProgress((++j) * step + 3 + i * proofs.length);
            }
            if (step == 0) {
                setProgress(10 + i * proofs.length);
            }

            // TODO: refactor Proof.setNamespaces() so this becomes unnecessary
            proofs[i].setNamespaces(proofs[i].getNamespaces());
            populateNamespaces(proofs[i]);
        }
    }

    /**
     * Creates an initConfig / a proof environment and reads an EnvInput into it
     */
    public InitConfig prepare(EnvInput envInput) throws ProofInputException {
        // The synchronized statement is required for thread save parsing since all JavaCC parser
        // are generated static.
        // For our own parser (ProofJavaParser.jj and SchemaJavaParser.jj) it is possible to
        // generate them non static
        // which is done on branch "hentschelJavaCCInstanceNotStatic". But recoder still uses static
        // methods and
        // the synchronized statement can not be avoided for this reason.

        synchronized (SchemaJavaParser.class) {
            // It is required to work with a copy to make this method thread save required by the
            // Eclipse plug-ins.
            InitConfig currentBaseConfig = baseConfig != null ? baseConfig.copy() : null;
            progressStarted(this);
            alreadyParsed.clear();

            // the first time, read in standard rules
            Profile profile = services.getProfile();
            if (currentBaseConfig == null || profile != currentBaseConfig.getProfile()) {
                currentBaseConfig = new InitConfig(services);
                RuleSource tacletBase = profile.getStandardRules().getTacletBase();
                if (tacletBase != null) {
                    KeYFile tacletBaseFile = new KeYFile("taclet base",
                        profile.getStandardRules().getTacletBase(), progMon, profile);
                    readEnvInput(tacletBaseFile, currentBaseConfig);
                }
                // remove traces of the generic sorts within the base configuration
                cleanupNamespaces(currentBaseConfig);
                baseConfig = currentBaseConfig;
            }
            InitConfig ic = prepare(envInput, currentBaseConfig);
            if (Debug.ENABLE_DEBUG) {
                print(ic);
            }
            return ic;
        }
    }

    private void print(Proof firstProof) {
        File taclets1;
        try {
            taclets1 = File.createTempFile("proof", ".txt");
        } catch (IOException e) {
            LOGGER.warn("Failed to create temp file", e);
            return;
        }
        LOGGER.debug("Taclets under: {}", taclets1);
        try (PrintWriter out =
            new PrintWriter(new BufferedWriter(new FileWriter(taclets1, StandardCharsets.UTF_8)))) {
            out.print(firstProof.toString());
        } catch (IOException e) {
            LOGGER.warn("Failed write proof", e);
        }
    }

    private void print(InitConfig ic) {
        File taclets1;
        try {
            taclets1 = File.createTempFile("taclets", ".txt");
        } catch (IOException e) {
            LOGGER.warn("Failed to create temp file", e);
            return;
        }
        LOGGER.debug("Taclets under: {}", taclets1);
        try (PrintWriter out =
            new PrintWriter(new BufferedWriter(new FileWriter(taclets1, StandardCharsets.UTF_8)))) {
            out.format("Date: %s%n", new Date());

            out.format("Choices: %n");
            ic.getActivatedChoices().forEach(i -> out.format("\t%s%n", i));

            out.format("Activated Taclets: %n");
            final List<Taclet> taclets = new ArrayList<>();
            taclets.addAll(ic.activatedTaclets());
            taclets.sort(Comparator.comparing(a -> a.name().toString()));
            for (Taclet taclet : taclets) {
                out.format("== %s (%s) =========================================%n", taclet.name(),
                    taclet.displayName());
                out.println(taclet);
                out.format("-----------------------------------------------------%n");
            }
        } catch (IOException e) {
            LOGGER.warn("Failed to save", e);
        }
    }

    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    private InitConfig prepare(EnvInput envInput, InitConfig referenceConfig)
            throws ProofInputException {
        // create initConfig
        InitConfig initConfig = referenceConfig.copy();


        // read Java
        readJava(envInput, initConfig);

        // register function and predicate symbols defined by Java program
        final JavaInfo javaInfo = initConfig.getServices().getJavaInfo();
        final Namespace<Function> functions = initConfig.getServices().getNamespaces().functions();
        final HeapLDT heapLDT = initConfig.getServices().getTypeConverter().getHeapLDT();
        assert heapLDT != null;
        if (javaInfo != null) {
            for (KeYJavaType kjt : javaInfo.getAllKeYJavaTypes()) {
                final Type type = kjt.getJavaType();
                if (type instanceof ClassDeclaration || type instanceof InterfaceDeclaration) {
                    for (Field f : javaInfo.getAllFields((TypeDeclaration) type)) {
                        final ProgramVariable pv = (ProgramVariable) f.getProgramVariable();
                        if (pv instanceof LocationVariable) {
                            heapLDT.getFieldSymbolForPV((LocationVariable) pv,
                                initConfig.getServices());
                        }
                    }
                }
                for (ProgramMethod pm : javaInfo.getAllProgramMethodsLocallyDeclared(kjt)) {
                    if (pm == null) {
                        continue; // weigl 2021-11-10
                    }
                    if (!(pm.isVoid() || pm.isConstructor())) {
                        functions.add(pm);
                    }
                }
            }
        } else {
            throw new ProofInputException("Problem initialization without JavaInfo!");
        }

        // read envInput
        readEnvInput(envInput, initConfig);

        // remove generic sorts defined in KeY file
        cleanupNamespaces(initConfig);

        // done
        progressStopped(this);
        return initConfig;
    }

    public ProofAggregate startProver(InitConfig initConfig, ProofOblInput po)
            throws ProofInputException {
        progressStarted(this);
        try {
            // determine environment
            initConfig = determineEnvironment(po, Objects.requireNonNull(initConfig));

            // read problem
            reportStatus("Loading problem \"" + po.name() + "\"");
            po.readProblem();
            ProofAggregate pa = po.getPO();
            // final work
            setUpProofHelper(po, pa);

            if (Debug.ENABLE_DEBUG) {
                print(pa.getFirstProof());
            }

            // done
            proofCreated(pa);
            return pa;
        } catch (ProofInputException e) {
            reportException(po, e);
            throw e;
        } finally {
            progressStopped(this);
        }
    }


    public ProofAggregate startProver(EnvInput envInput, ProofOblInput po)
            throws ProofInputException {
        return startProver(prepare(envInput), po);
    }

    public void tryReadProof(IProofFileParser pfp, KeYUserProblemFile kupf)
            throws ProofInputException {
        reportStatus("Loading proof", kupf.getNumberOfChars());
        try {
            kupf.readProof(pfp);
            setProgress(kupf.getNumberOfChars() / 2);
        } catch (IOException e) {
            throw new ProofInputException(e);
        } finally {
            kupf.close();
            setProgress(kupf.getNumberOfChars());
        }
    }

    /**
     * Returns the found warnings.
     *
     * @return The found warnings.
     */
    public ImmutableSet<PositionedString> getWarnings() {
        return warnings;
    }

    /**
     * Sets the FileRepo responsible for consistency between source code and proof.
     *
     * @param fileRepo the FileRepo to set
     */
    public void setFileRepo(FileRepo fileRepo) {
        this.fileRepo = fileRepo;
    }

    public ProblemInitializerListener getListener() {
        return listener;
    }

    public ProgressMonitor getProgMon() {
        return progMon;
    }

    public interface ProblemInitializerListener {
        void proofCreated(ProblemInitializer sender, ProofAggregate proofAggregate);

        void progressStarted(Object sender);

        void progressStopped(Object sender);

        void reportStatus(Object sender, String status, int progress);

        void reportStatus(Object sender, String status);

        void resetStatus(Object sender);

        void reportException(Object sender, ProofOblInput input, Exception e);

        default void showIssueDialog(Collection<PositionedString> issues) {}
    }
}
