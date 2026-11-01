/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.proof.io;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.net.MalformedURLException;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.stream.Collectors;

import de.uka.ilkd.key.nparser.*;
import de.uka.ilkd.key.nparser.builder.ContractsAndInvariantsFinder;
import de.uka.ilkd.key.nparser.builder.ProblemFinder;
import de.uka.ilkd.key.nparser.builder.TacletPBuilder;
import de.uka.ilkd.key.proof.init.*;
import de.uka.ilkd.key.proof.io.consistency.FileRepo;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.util.ProgressMonitor;
import de.uka.ilkd.key.util.parsing.BuildingException;
import de.uka.ilkd.key.util.parsing.BuildingIssue;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.collection.Immutables;
import org.key_project.util.parsing.Location;

import org.antlr.v4.runtime.misc.ParseCancellationException;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;


/**
 * Represents an input from a .key file producing an environment.
 */
@NullMarked
public class KeYFile implements EnvInput {
    private static final Logger LOGGER = LoggerFactory.getLogger(KeYFile.class);

    /**
     * the RuleSource delivering the input stream for the file.
     */
    protected final RuleSource file;

    /**
     * the graphical entity to notify on the state of reading.
     */
    protected final @Nullable ProgressMonitor monitor;
    private final String name;
    protected @Nullable Profile profile;
    protected @Nullable InitConfig initConfig;
    private KeyAst.@Nullable File fileCtx = null;
    private @Nullable ProblemFinder problemFinder = null;
    private @Nullable ProblemInformation problemInformation = null;
    private @Nullable Includes includes;

    /**
     * The FileRepo that will store the files.
     */
    private @Nullable FileRepo fileRepo;

    /// creates a new representation for a given file by indicating a name and a RuleSource
    /// representing the physical source of the .key file.
    ///
    /// @param profile if non-null, enforces to use the given profile. Use `null` if the profile
    /// from the {@link KeYUserProblemFile} or {@link AbstractProfile#getDefaultProfile()} shoudl be
    /// used.
    public KeYFile(String name, RuleSource file, @Nullable ProgressMonitor monitor,
            @Nullable Profile profile) {
        this.name = Objects.requireNonNull(name);
        this.file = Objects.requireNonNull(file);
        this.monitor = monitor;
        this.profile = profile;
    }


    /**
     * creates a new representation for a given file by indicating a name and a RuleSource
     * representing the physical source of the .key file.
     *
     * @param name the name of the file
     * @param file the physical rule source of the .key file
     * @param monitor monitor for reporting progress
     * @param profile the profile
     * @param fileRepo the FileRepo which will store the file, or null if no consistency tracking is
     *        desired
     */
    public KeYFile(String name, RuleSource file, @Nullable ProgressMonitor monitor,
            @Nullable Profile profile, @Nullable FileRepo fileRepo) {
        this(name, file, monitor, profile);
        this.fileRepo = fileRepo;
    }

    /**
     * creates a new representation for a given file by indicating a name and a file representing
     * the physical source of the .key file.
     */
    public KeYFile(String name, Path file, @Nullable ProgressMonitor monitor,
            @Nullable Profile profile) {
        this(name, RuleSourceFactory.initRuleFile(file, false), monitor, profile);
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
    public KeYFile(String name, Path file, ProgressMonitor monitor, Profile profile,
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
     * @param profile the KeY profile under which the file is to be load, or {@code null} to
     *        respect the profile declared in the file
     * @param compressed <code>true</code> iff the file has compressed content
     */
    public KeYFile(String name, Path file, FileRepo fileRepo, ProgressMonitor monitor,
            @Nullable Profile profile, boolean compressed) {
        this(name, RuleSourceFactory.initRuleFile(file, compressed), monitor, profile);
        this.fileRepo = fileRepo;
    }

    protected InputStream getNewStream() throws FileNotFoundException {
        close();
        if (!file.isAvailable()) {
            throw new FileNotFoundException("File/Resource " + file + " not found.");
        }
        // open a stream to the file (via FileRepo if possible)
        try {
            InputStream input = null;
            if (fileRepo != null) {
                input = fileRepo.getInputStream(file);
            }
            // fallback (e.g. used for *.proof.gz files)
            return input != null ? input : file.getNewStream();
        } catch (IOException e) {
            LOGGER.warn("Failed to open new stream", e);
            throw new FileNotFoundException("Failed to open new stream: " + file);
        }
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

    /**
     * Returns the proof preferences, reading and installing them into the init config on first
     * access.
     *
     * @return The proof preferences (may be {@code null} if none are stored).
     *         <p>
     *         The init config is set before the preferences are read; the dereferences of the
     *         (nullable)
     *         init-config field are suppressed with a scoped key. The preferences read from the
     *         file may
     *         likewise be {@code null} (none stored, e.g. for directory inputs); they are stored
     *         as-is, so
     *         the {@code setSettings} argument type mismatch is suppressed as well.
     */
    @SuppressWarnings({ "nullness:dereference.of.nullable", "nullness:argument.type.incompatible" })
    protected @Nullable ProofSettings getPreferences() {
        if (initConfig.getSettings() == null) {
            var settings = readPreferences();
            initConfig.setSettings(settings);
            return settings;
        }
        return initConfig.getSettings();
    }

    public @Nullable ProofSettings readPreferences() {
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
                includes = ctx.getIncludes(Objects.requireNonNull(file.file().getParent()));
            } catch (ParseCancellationException e) {
                throw new ParseCancellationException(e);
            } catch (Exception e) {
                throw new ProofInputException(e);
            }
        }
        return includes;
    }


    /**
     * Normalizes a path string read from a KeY/proof file so that it can be parsed by
     * {@link Paths#get(String, String...)} on the current platform. KeY now always writes path
     * separators as forward slashes, but proofs saved by older versions on Windows may contain
     * backslashes. On POSIX a backslash is a valid file-name character, so such a path would not be
     * split into segments and could not be resolved. Converting backslashes to forward slashes is
     * safe on all platforms (Windows accepts '/' as a separator) and keeps these legacy proofs
     * loadable.
     *
     * @param path the raw path string as stored in the file
     * @return the path string with backslashes replaced by forward slashes
     */
    private static String normalizeStoredPath(String path) {
        return path.replace('\\', '/');
    }

    /**
     * The parsed file is a regular {@code .key} file whose parent directory is guaranteed to be
     * non-{@code null}; the dereferences of the (nullable) parent-directory paths are suppressed
     * with a scoped key.
     */
    @Override
    @SuppressWarnings("nullness:dereference.of.nullable")
    public @Nullable Path readBootClassPath() {
        ProblemInformation pi = getProblemInformation();
        String bootClassPath = pi.getBootClassPath();
        if (bootClassPath == null) {
            return null;
        }
        Path bootClassPathFile = Paths.get(normalizeStoredPath(bootClassPath));
        if (!bootClassPathFile.isAbsolute()) {
            // convert to absolute by resolving against the parent path of the parsed file
            Path parentDirectory = file.file().getParent();
            bootClassPathFile = parentDirectory.resolve(bootClassPathFile).normalize();
        }
        if (!Files.isDirectory(bootClassPathFile)) {
            // Report the missing directory at the \bootclasspath declaration in the .key file,
            // rather than letting it surface later as a bare exception with no source location.
            throw new BuildingException(locationOrUndefined(pi, bootClassPath), String.format(
                "The \\bootclasspath \"%s\" does not exist or is not a directory.",
                bootClassPathFile));
        }
        return bootClassPathFile;
    }

    /**
     * @return the location at which {@code path} was declared in this file, or
     *         {@link Location#UNDEFINED} if it is unknown
     */
    private static Location locationOrUndefined(ProblemInformation pi, String path) {
        Location loc = pi.getPathLocation(path);
        return loc != null ? loc : Location.UNDEFINED;
    }

    protected @NonNull ProblemInformation getProblemInformation() {
        if (problemInformation == null) {
            KeyAst.File ctx = getParseContext();
            problemInformation = ctx.getProblemInformation();
        }
        return problemInformation;
    }


    /**
     * The parsed file is a regular {@code .key} file whose parent directory is guaranteed to be
     * non-{@code null}; the dereference of the (nullable) parent-directory path is suppressed
     * with a scoped key. A {@code \classpath} declaration without a value yields a {@code null}
     * entry that is deliberately kept in the returned list; the argument suppression is scoped
     * to that case.
     */
    @Override
    @SuppressWarnings({ "nullness:dereference.of.nullable", "nullness:argument.type.incompatible" })
    public @NonNull List<Path> readClassPath() {
        ProblemInformation pi = getProblemInformation();
        Path parentDirectory = file.file().getParent();
        List<Path> fileList = new ArrayList<>();
        for (String cp : pi.getClasspath()) {
            if (cp == null) {
                fileList.add(null);
            } else {
                var f = Paths.get(normalizeStoredPath(cp));
                if (!f.isAbsolute()) {
                    f = parentDirectory.resolve(f).normalize();
                }
                if (!Files.exists(f)) {
                    // Point at the \classpath declaration in the .key file instead of letting the
                    // missing directory surface later as a bare, source-less exception.
                    throw new BuildingException(locationOrUndefined(pi, cp),
                        String.format("The \\classpath entry \"%s\" does not exist.", f));
                }
                fileList.add(f);
            }
        }
        return fileList;
    }

    @Override
    public @Nullable Path readJavaPath() throws ProofInputException {
        ProblemInformation pi = getProblemInformation();
        String javaPath = pi.getJavaSource();
        if (javaPath != null) {
            javaPath = normalizeStoredPath(javaPath);
            Path absFile = Paths.get(javaPath);
            if (!absFile.isAbsolute()) {
                // convert to absolute by resolving against the parent path of the parsed file
                Path parent = file.file().getParent();
                if (parent == null) {
                    parent = Path.of(".");
                }
                absFile = parent.resolve(javaPath).normalize();
            }
            if (!Files.exists(absFile)) {
                throw new ProofInputException(String.format(
                    "The \\javaSource declared in %s could not be found.%n"
                        + "    declared:    \"%s\"%n"
                        + "    expected at: %s",
                    file.file().getFileName(), javaPath, absFile.toAbsolutePath()));
            }
            return absFile.toAbsolutePath();
        }
        return null;
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
     *         <p>
     *         Although {@code initConfig} is null-checked at the entry, the subsequent parser
     *         access is
     *         seen as potentially re-assigning the field; the dereferences are suppressed with a
     *         scoped
     *         key.
     */
    @SuppressWarnings("nullness:dereference.of.nullable")
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
     *         <p>
     *         The init config is set before contracts are read; the dereferences of the (nullable)
     *         init-config field are suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:dereference.of.nullable")
    public ImmutableSet<PositionedString> readContracts() {
        SpecificationRepository specRepos = initConfig.getServices().getSpecificationRepository();
        ContractsAndInvariantsFinder cinvs =
            new ContractsAndInvariantsFinder(initConfig.getServices(), initConfig.namespaces());
        getParseContext().accept(cinvs);
        specRepos.addContracts(Immutables.createSetFrom(cinvs.getContracts()));
        specRepos.addClassInvariants(Immutables.createSetFrom(cinvs.getInvariants()));

        return DefaultImmutableSet.nil();
    }

    /**
     * Returns the problem finder, creating it from the init config on first access.
     *
     * @return The problem finder.
     *         <p>
     *         The init config is set before the problem finder is created; the dereferences of the
     *         (nullable) init-config field are suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:dereference.of.nullable")
    protected @NonNull ProblemFinder getProblemFinder() {
        if (problemFinder == null) {
            ProblemFinder finder =
                new ProblemFinder(initConfig.getServices(), initConfig.namespaces());
            getParseContext().accept(finder);
            problemFinder = finder;
        }
        return problemFinder;
    }


    /**
     * reads the sorts declaration of the .key file only, modifying the sort namespace of the
     * initial configuration
     * <p>
     * The init config is set before sorts are read; the dereferences of the (nullable)
     * init-config field are suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:dereference.of.nullable")
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
     *         <p>
     *         The init config is set before functions and predicates are read; the dereferences of
     *         the
     *         (nullable) init-config field are suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:dereference.of.nullable")
    public List<PositionedString> readFuncAndPred() {
        if (file == null) {
            return Collections.emptyList();
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
     *         <p>
     *         The init config is set before rules are read; the dereferences of the (nullable)
     *         init-config field are suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:dereference.of.nullable")
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
                    new Location(
                        Objects.requireNonNull(file != null
                                ? new URL(file.getExternalForm()).toURI()
                                : null),
                        w.position()));
            } catch (MalformedURLException | URISyntaxException e) {
                throw new RuntimeException(e);
            }
        })
                .collect(Collectors.<PositionedString>toList());
    }

    public @Nullable String chooseContract() {
        return null;
    }

    public @Nullable Configuration getProofObligation() {
        return null;
    }


    @Override
    public String toString() {
        return name() + " " + file.toString();
    }


    @Override
    public boolean equals(@Nullable Object o) {
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
        return profile == null ? getDefaultProfile() : profile;
    }

    /// Returns the default profile.
    public Profile getDefaultProfile() {
        return AbstractProfile.getDefaultProfile();
    }

    @Override
    public @Nullable Path getInitialFile() {
        return file != null ? file.file() : null;
    }
}
