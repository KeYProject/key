/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.io;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.net.MalformedURLException;
import java.net.URISyntaxException;
import java.net.URL;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;

import de.uka.ilkd.key.nparser.*;
import de.uka.ilkd.key.nparser.builder.ContractsAndInvariantsFinder;
import de.uka.ilkd.key.nparser.builder.ProblemFinder;
import de.uka.ilkd.key.nparser.builder.TacletPBuilder;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.init.Includes;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.consistency.FileRepo;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.util.ProgressMonitor;
import de.uka.ilkd.key.util.parsing.BuildingIssue;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;


/**
 * Represents an input from a .key file producing an environment.
 */
public class KeYFile implements EnvInput {
    private static final Logger LOGGER = LoggerFactory.getLogger(KeYFile.class);

    /**
     * the RuleSource delivering the input stream for the file.
     */
    protected final RuleSource file;
    /**
     * the graphical entity to notify on the state of reading.
     */
    protected final ProgressMonitor monitor;
    private final String name;
    private final Profile profile;
    protected InitConfig initConfig;
    private KeyAst.File fileCtx = null;
    @Nullable
    private ProblemFinder problemFinder = null;
    @Nullable
    private ProblemInformation problemInformation = null;
    private Includes includes;

    /**
     * The FileRepo that will store the files.
     */
    private FileRepo fileRepo;

    /**
     * creates a new representation for a given file by indicating a name and a RuleSource
     * representing the physical source of the .key file.
     */
    public KeYFile(String name, RuleSource file, ProgressMonitor monitor, Profile profile) {
        this.name = Objects.requireNonNull(name);
        this.file = Objects.requireNonNull(file);
        this.monitor = monitor;
        this.profile = Objects.requireNonNull(profile);
    }


    /**
     * creates a new representation for a given file by indicating a name and a RuleSource
     * representing the physical source of the .key file.
     *
     * @param name the name of the file
     * @param file the physical rule source of the .key file
     * @param monitor monitor for reporting progress
     * @param profile the profile
     * @param fileRepo the FileRepo which will store the file
     */
    public KeYFile(String name, RuleSource file, ProgressMonitor monitor, Profile profile,
            FileRepo fileRepo) {
        this(name, file, monitor, profile);
        this.fileRepo = fileRepo;
    }

    /**
     * creates a new representation for a given file by indicating a name and a file representing
     * the physical source of the .key file.
     */
    public KeYFile(String name, File file, ProgressMonitor monitor, Profile profile) {
        this(name, file, monitor, profile, false);
    }

    /**
     * Creates a new representation for a given file by indicating a name and a file representing
     * the physical source of the .key file.
     *
     * @param name the name of the resource
     * @param file the file to find it
     * @param monitor a possibly null reference to a monitor for the loading progress
     * @param profile the KeY profile under which the file is to be load
     * @param compressed <code>true</code> iff the file has compressed content
     */
    public KeYFile(String name, File file, ProgressMonitor monitor, Profile profile,
            boolean compressed) {
        this(name, RuleSourceFactory.initRuleFile(file, compressed), monitor, profile);
    }


    /**
     * Creates a new representation for a given file by indicating a name and a file representing
     * the physical source of the .key file.
     *
     * @param name the name of the resource
     * @param file the file to find it
     * @param fileRepo the FileRepo which will store the file
     * @param monitor a possibly null reference to a monitor for the loading progress
     * @param profile the KeY profile under which the file is to be load
     * @param compressed <code>true</code> iff the file has compressed content
     */
    public KeYFile(String name, File file, FileRepo fileRepo, ProgressMonitor monitor,
            Profile profile, boolean compressed) {
        this(name, RuleSourceFactory.initRuleFile(file, compressed), monitor, profile);
        this.fileRepo = fileRepo;
    }

    protected InputStream getNewStream() throws FileNotFoundException {
        close();
        if (!file.isAvailable()) {
            throw new FileNotFoundException("File/Resource " + file + " not found.");
        }
        // open a stream to the file (via FileRepo if possible)
        InputStream input = null;
        try {
            if (fileRepo != null) {
                input = fileRepo.getInputStream(file);
                // fallback (e.g. used for *.proof.gz files)
                if (input == null) {
                    input = file.getNewStream();
                }
            } else {
                input = file.getNewStream();
            }
        } catch (IOException e) {
            LOGGER.warn("Failed to open new stream", e);
        }
        return input;
    }

    protected KeyAst.File getParseContext() {
        if (fileCtx == null) {
            try {
                LOGGER.trace("Reading KeY file {}", file);
                fileCtx = ParsingFacade.parseFile(file.getCharStream());
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
        }
        return fileCtx;
    }

    protected ProofSettings getPreferences() {
        if (initConfig.getSettings() == null) {
            return readPreferences();
        } else {
            return initConfig.getSettings();
        }
    }

    public ProofSettings readPreferences() {
        if (file.isDirectory()) {
            return null;
        }
        KeyAst.File ctx = getParseContext();
        return ctx.findProofSettings();
    }

    @Override
    public String name() {
        return name;
    }


    @Override
    public int getNumberOfChars() {
        return file.getNumberOfBytes();
    }


    @Override
    public void setInitConfig(InitConfig conf) {
        this.initConfig = conf;
    }


    @Override
    public Includes readIncludes() throws ProofInputException {
        if (includes == null) {
            try {
                KeyAst.File ctx = getParseContext();
                includes =
                    ctx.getIncludes(file.file().getAbsoluteFile().getParentFile().toURI().toURL());
            } catch (Exception e) {
                throw new ProofInputException(e);
            }
        }
        return includes;
    }


    @Override
    public File readBootClassPath() {
        @NonNull
        ProblemInformation pi = getProblemInformation();
        String bootClassPath = pi.getBootClassPath();
        if (bootClassPath == null) {
            return null;
        }
        File bootClassPathFile = new File(bootClassPath);
        if (!bootClassPathFile.isAbsolute()) {
            // convert to absolute by resolving against the parent path of the parsed file
            String parentDirectory = file.file().getParent();
            bootClassPathFile = new File(parentDirectory, bootClassPath);
        }

        return bootClassPathFile;
    }

    protected @NonNull ProblemInformation getProblemInformation() {
        if (problemInformation == null) {
            KeyAst.File ctx = getParseContext();
            problemInformation = ctx.getProblemInformation();
        }
        return problemInformation;
    }


    @NonNull
    @Override
    public List<File> readClassPath() {
        @NonNull
        ProblemInformation pi = getProblemInformation();
        String parentDirectory = file.file().getParent();
        List<File> fileList = new ArrayList<>();
        for (String cp : pi.getClasspath()) {
            if (cp == null) {
                fileList.add(null);
            } else {
                File f = new File(cp);
                if (!f.isAbsolute()) {
                    f = new File(parentDirectory, cp);
                }
                fileList.add(f);
            }
        }
        return fileList;
    }

    @Override
    public String readJavaPath() throws ProofInputException {
        @NonNull
        ProblemInformation pi = getProblemInformation();
        String javaPath = pi.getJavaSource();
        if (javaPath != null) {
            File absFile = new File(javaPath);
            if (!absFile.isAbsolute()) {
                // convert to absolute by resolving against the parent path of the parsed file
                File parent = file.file().getParentFile();
                absFile = new File(parent, javaPath);
            }
            if (!absFile.exists()) {
                throw new ProofInputException(
                    String.format("Declared Java source %s not found.", javaPath));
            }
            return absFile.getAbsolutePath();
        }
        return javaPath;
    }


    @Override
    public ImmutableSet<PositionedString> read() throws ProofInputException {
        ImmutableSet<PositionedString> warnings = DefaultImmutableSet.nil();
        warnings = warnings.union(readExtendedSignature());
        warnings = warnings.union(readContracts());
        warnings = warnings.add(getPositionedStrings(readRules()));
        return warnings;
    }

    /**
     * reads sort, function and predicate declarations
     *
     * @return list of parser warnings
     */
    public ImmutableSet<PositionedString> readExtendedSignature() {
        if (initConfig == null) {
            throw new IllegalStateException("KeYFile: InitConfig not set.");
        }
        // read .key file
        ChoiceInformation ci = getParseContext().getChoices();
        initConfig.addCategory2DefaultChoices(ci.getDefaultOptions());

        var warnings = new ArrayList<PositionedString>();
        warnings.addAll(readSorts());
        warnings.addAll(readFuncAndPred());

        return DefaultImmutableSet.fromCollection(warnings);
    }

    /**
     * reads contracts and rule definitions
     *
     * @return list of parser warnings
     */
    public ImmutableSet<PositionedString> readContracts() {
        SpecificationRepository specRepos = initConfig.getServices().getSpecificationRepository();
        ContractsAndInvariantsFinder cinvs =
            new ContractsAndInvariantsFinder(initConfig.getServices(), initConfig.namespaces());
        getParseContext().accept(cinvs);
        specRepos.addContracts(ImmutableSet.fromCollection(cinvs.getContracts()));
        specRepos.addClassInvariants(ImmutableSet.fromCollection(cinvs.getInvariants()));

        return DefaultImmutableSet.nil();
    }

    @NonNull
    protected ProblemFinder getProblemFinder() {
        if (problemFinder == null) {
            problemFinder = new ProblemFinder(initConfig.getServices(), initConfig.namespaces());
            getParseContext().accept(problemFinder);
        }
        return problemFinder;
    }


    /**
     * reads the sorts declaration of the .key file only, modifying the sort namespace of the
     * initial configuration
     */
    public Collection<PositionedString> readSorts() {
        KeyAst.File ctx = getParseContext();
        KeyIO io = new KeyIO(initConfig.getServices(), initConfig.namespaces());
        io.evalDeclarations(ctx);
        ChoiceInformation choice = getParseContext().getChoices();
        // we ignore the namespace of choice finder.
        initConfig.addCategory2DefaultChoices(choice.getDefaultOptions());

        return io.getWarnings().stream().map(BuildingIssue::asPositionedString).toList();
    }


    /**
     * reads the functions and predicates declared in the .key file only, modifying the function
     * namespaces of the respective taclet options.
     *
     * @return warnings during the interpretation of the AST constructs
     */
    public List<PositionedString> readFuncAndPred() {
        if (file == null) {
            return null;
        }
        KeyAst.File ctx = getParseContext();
        KeyIO io = new KeyIO(initConfig.getServices(), initConfig.namespaces());
        io.evalFuncAndPred(ctx);
        return io.getWarnings().stream().map(BuildingIssue::asPositionedString).toList();
    }


    /**
     * reads the rules and problems declared in the .key file only, modifying the set of rules of
     * the initial configuration
     *
     * @return list of issues that occurred during parsing the taclets
     */
    public List<BuildingIssue> readRules() {
        KeyAst.File ctx = getParseContext();
        TacletPBuilder visitor = new TacletPBuilder(initConfig.getServices(),
            initConfig.namespaces(), initConfig.getTaclet2Builder());
        ctx.accept(visitor);
        List<Taclet> taclets = visitor.getTopLevelTaclets();
        initConfig.addTaclets(taclets);

        return visitor.getBuildingIssues();
    }


    public void close() {
        fileCtx = null;
        problemFinder = null;
        problemInformation = null;
    }

    /**
     * constructs positioned strings from {@link BuildingIssue}s such that they can be displayed
     * like other issues
     *
     * @param issues the {@link BuildingIssue}s to be converted into {@link PositionedString}s
     * @return list containing a {@link PositionedString} for each {@link BuildingIssue}
     *         in <code>issues</code>
     */
    protected List<PositionedString> getPositionedStrings(List<BuildingIssue> issues) {
        return issues.stream().map(w -> {
            try {
                return new PositionedString(w.message(),
                    new Location(file != null ? new URL(file.getExternalForm()).toURI() : null,
                        w.position()));
            } catch (MalformedURLException | URISyntaxException e) {
                throw new RuntimeException(e);
            }
        })
                .collect(Collectors.<PositionedString>toList());
    }

    public String chooseContract() {
        return null;
    }

    public Configuration getProofObligation() {
        return null;
    }


    @Override
    public String toString() {
        return name() + " " + file.toString();
    }


    @Override
    public boolean equals(Object o) {
        if (o == null || o.getClass() != this.getClass()) {
            return false;
        }
        KeYFile kf = (KeYFile) o;
        return kf.file.getExternalForm().equals(file.getExternalForm());

    }


    @Override
    public int hashCode() {
        final String externalForm = file.getExternalForm();
        if (externalForm == null) {
            return -1;
        }
        return externalForm.hashCode();
    }

    @Override
    public Profile getProfile() {
        return profile;
    }

    @Override
    public File getInitialFile() {
        return file != null ? file.file() : null;
    }
}
