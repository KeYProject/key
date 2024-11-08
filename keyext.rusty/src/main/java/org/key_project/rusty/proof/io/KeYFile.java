/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof.io;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;

import org.key_project.logic.Name;
import org.key_project.rusty.parser.*;
import org.key_project.rusty.parser.builder.ProblemFinder;
import org.key_project.rusty.parser.builder.TacletPBuilder;
import org.key_project.rusty.proof.init.Includes;
import org.key_project.rusty.proof.init.InitConfig;
import org.key_project.rusty.proof.init.Profile;
import org.key_project.rusty.proof.init.ProofInputException;
import org.key_project.rusty.proof.io.consistency.FileRepo;
import org.key_project.rusty.rule.Taclet;
import org.key_project.rusty.settings.Configuration;
import org.key_project.rusty.settings.ProofSettings;
import org.key_project.rusty.util.parsing.BuildingIssue;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.NonNull;

/**
 * Represents an input from a .key file producing an environment.
 */
public class KeYFile implements EnvInput {
    /**
     * the RuleSource delivering the input stream for the file.
     */
    protected final RuleSource file;

    private final Name name;
    private final Profile profile;
    protected InitConfig initConfig;
    private KeYAst.File fileCtx = null;
    private Includes includes;
    private ProblemInformation problemInformation;

    /**
     * The FileRepo that will store the files.
     */
    private FileRepo fileRepo;
    private ProblemFinder problemFinder;

    /**
     * creates a new representation for a given file by indicating a name and a RuleSource
     * representing the physical source of the .key file.
     */
    public KeYFile(String name, RuleSource file, Profile profile) {
        this.name = new Name(name);
        this.file = Objects.requireNonNull(file);
        this.profile = Objects.requireNonNull(profile);
    }

    /**
     * creates a new representation for a given file by indicating a name and a RuleSource
     * representing the physical source of the .key file.
     *
     * @param name the name of the file
     * @param file the physical rule source of the .key file
     * @param profile the profile
     * @param fileRepo the FileRepo which will store the file
     */
    public KeYFile(String name, RuleSource file, Profile profile,
            FileRepo fileRepo) {
        this(name, file, profile);
        this.fileRepo = fileRepo;
    }

    /**
     * creates a new representation for a given file by indicating a name and a file representing
     * the physical source of the .key file.
     */
    public KeYFile(String name, File file, Profile profile) {
        this(name, file, profile, false);
    }

    /**
     * Creates a new representation for a given file by indicating a name and a file representing
     * the physical source of the .key file.
     *
     * @param name the name of the resource
     * @param file the file to find it
     * @param profile the KeY profile under which the file is to be load
     * @param compressed <code>true</code> iff the file has compressed content
     */
    public KeYFile(String name, File file, Profile profile,
            boolean compressed) {
        this(name, RuleSourceFactory.initRuleFile(file, compressed), profile);
    }

    /**
     * Creates a new representation for a given file by indicating a name and a file representing
     * the physical source of the .key file.
     *
     * @param name the name of the resource
     * @param file the file to find it
     * @param fileRepo the FileRepo which will store the file
     * @param profile the KeY profile under which the file is to be load
     * @param compressed <code>true</code> iff the file has compressed content
     */
    public KeYFile(String name, File file, FileRepo fileRepo,
            Profile profile, boolean compressed) {
        this(name, RuleSourceFactory.initRuleFile(file, compressed), profile);
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

        }
        return input;
    }

    protected KeYAst.File getParseContext() {
        if (fileCtx == null) {
            try {
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
        KeYAst.File ctx = getParseContext();
        return ctx.findProofSettings();
    }

    @Override
    public @NonNull Name name() {
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
                KeYAst.File ctx = getParseContext();
                includes =
                    ctx.getIncludes(file.file().getAbsoluteFile().getParentFile().toURI().toURL());
            } catch (Exception e) {
                throw new ProofInputException(e);
            }
        }
        return includes;
    }

    protected @NonNull ProblemInformation getProblemInformation() {
        if (problemInformation == null) {
            KeYAst.File ctx = getParseContext();
            problemInformation = ctx.getProblemInformation();
        }
        return problemInformation;
    }

    @Override
    public String readRustPath() throws ProofInputException {
        ProblemInformation pi = getProblemInformation();
        String rustPath = pi.getRustSource();
        if (rustPath != null) {
            File absFile = new File(rustPath);
            if (!absFile.isAbsolute()) {
                // convert to absolute by resolving against the parent path of the parsed file
                File parent = file.file().getParentFile();
                absFile = new File(parent, rustPath);
            }
            if (!absFile.exists()) {
                throw new ProofInputException(
                    String.format("Declared Rust source %s not found.", rustPath));
            }
            return absFile.getAbsolutePath();
        }
        return rustPath;
    }

    @Override
    public ImmutableSet<String> read() throws ProofInputException {
        ImmutableSet<String> warnings = DefaultImmutableSet.nil();
        warnings = warnings.union(readExtendedSignature());
        // warnings = warnings.union(readContracts());
        warnings = warnings.add(getPositionedStrings(readRules()));
        return warnings;
    }

    /**
     * reads sort, function and predicate declarations
     *
     * @return list of parser warnings
     */
    public ImmutableSet<String> readExtendedSignature() {
        if (initConfig == null) {
            throw new IllegalStateException("KeYFile: InitConfig not set.");
        }
        // read .key file
        ChoiceInformation ci = getParseContext().getChoices();
        initConfig.addCategory2DefaultChoices(ci.getDefaultOptions());

        var warnings = new ArrayList<String>();
        warnings.addAll(readSorts());
        warnings.addAll(readFuncAndPred());

        return DefaultImmutableSet.fromCollection(warnings);
    }

    /**
     * reads contracts and rule definitions
     *
     * @return list of parser warnings
     */
    /*
     * public ImmutableSet<String> readContracts() {
     * SpecificationRepository specRepos = initConfig.getServices().getSpecificationRepository();
     * ContractsAndInvariantsFinder cinvs =
     * new ContractsAndInvariantsFinder(initConfig.getServices(), initConfig.namespaces());
     * getParseContext().accept(cinvs);
     * specRepos.addContracts(Immutables.createSetFrom(cinvs.getContracts()));
     * specRepos.addClassInvariants(Immutables.createSetFrom(cinvs.getInvariants()));
     *
     * return DefaultImmutableSet.nil();
     * }
     */

    protected @NonNull ProblemFinder getProblemFinder() {
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
    public Collection<String> readSorts() {
        KeYAst.File ctx = getParseContext();
        KeYIO io = new KeYIO(initConfig.getServices(), initConfig.namespaces());
        io.evalDeclarations(ctx);

        return io.getWarnings().stream().map(BuildingIssue::message).toList();
    }

    /**
     * reads the functions and predicates declared in the .key file only, modifying the function
     * namespaces of the respective taclet options.
     *
     * @return warnings during the interpretation of the AST constructs
     */
    public List<String> readFuncAndPred() {
        if (file == null) {
            return null;
        }
        KeYAst.File ctx = getParseContext();
        KeYIO io = new KeYIO(initConfig.getServices(), initConfig.namespaces());
        io.evalFuncAndPred(ctx);
        return io.getWarnings().stream().map(BuildingIssue::message).toList();
    }

    /**
     * reads the rules and problems declared in the .key file only, modifying the set of rules of
     * the initial configuration
     *
     * @return list of issues that occurred during parsing the taclets
     */
    public List<BuildingIssue> readRules() {
        KeYAst.File ctx = getParseContext();
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
     * @param issues the {@link BuildingIssue}s to be converted into {@link String}s
     * @return list containing a {@link String} for each {@link BuildingIssue}
     *         in <code>issues</code>
     */
    protected List<String> getPositionedStrings(List<BuildingIssue> issues) {
        return issues.stream().map(BuildingIssue::message)
                .collect(Collectors.<String>toList());
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
