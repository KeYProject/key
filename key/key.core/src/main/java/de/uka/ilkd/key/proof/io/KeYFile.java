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

import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.nparser.ParsingFacade;
import de.uka.ilkd.key.nparser.ProblemInformation;
import de.uka.ilkd.key.nparser.builder.ContractsAndInvariantsFinder;
import de.uka.ilkd.key.nparser.builder.ProblemFinder;
import de.uka.ilkd.key.nparser.builder.TacletPBuilder;
import de.uka.ilkd.key.proof.init.Includes;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.consistency.FileRepo;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ProgressMonitor;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;


/**
 * Represents an input from a .key file producing an environment.
 */
public class KeYFile implements EnvInput {
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
    private KeyAst.File ctx = null;
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
     * creates a new representation for a given file by indicating a name
     * and a RuleSource representing the physical source of the .key file.
     */
    public KeYFile(String name,
                   RuleSource file,
                   ProgressMonitor monitor,
                   Profile profile) {
        assert name != null;
        assert file != null;
        assert profile != null;
        this.name = name;
        this.file = file;
        this.monitor = monitor;
        this.profile = profile;
    }


    /**
     * creates a new representation for a given file by indicating a name
     * and a RuleSource representing the physical source of the .key file.
     *
     * @param name     the name of the file
     * @param file     the physical rule source of the .key file
     * @param monitor  monitor for reporting progress
     * @param profile  the profile
     * @param fileRepo the FileRepo which will store the file
     */
    public KeYFile(String name,
                   RuleSource file,
                   ProgressMonitor monitor,
                   Profile profile,
                   FileRepo fileRepo) {
        this(name, file, monitor, profile);
        this.fileRepo = fileRepo;
    }

    /**
     * creates a new representation for a given file by indicating a name
     * and a file representing the physical source of the .key file.
     */
    public KeYFile(String name,
                   File file,
                   ProgressMonitor monitor,
                   Profile profile) {
        this(name, file, monitor, profile, false);
    }

    /**
     * Creates a new representation for a given file by indicating a name and a
     * file representing the physical source of the .key file.
     *
     * @param name       the name of the resource
     * @param file       the file to find it
     * @param monitor    a possibly null reference to a monitor for the loading
     *                   progress
     * @param profile    the KeY profile under which the file is to be load
     * @param compressed <code>true</code> iff the file has compressed content
     */
    public KeYFile(String name,
                   File file,
                   ProgressMonitor monitor,
                   Profile profile,
                   boolean compressed) {
        this(name, RuleSourceFactory.initRuleFile(file, compressed), monitor, profile);
    }

    /*
    private KeYParserF createDeclParser(InputStream is) throws IOException {
        return new KeYParserF(ParserMode.DECLARATION,
                             new KeYLexerF(is,
                                          file.toString()),
                             initConfig.getServices(),
                             initConfig.namespaces());
    }
    */

    /**
     * Creates a new representation for a given file by indicating a name and a
     * file representing the physical source of the .key file.
     *
     * @param name       the name of the resource
     * @param file       the file to find it
     * @param fileRepo   the FileRepo which will store the file
     * @param monitor    a possibly null reference to a monitor for the loading
     *                   progress
     * @param profile    the KeY profile under which the file is to be load
     * @param compressed <code>true</code> iff the file has compressed content
     */
    public KeYFile(String name,
                   File file,
                   FileRepo fileRepo,
                   ProgressMonitor monitor,
                   Profile profile,
                   boolean compressed) {
        this(name,
                RuleSourceFactory.initRuleFile(file, compressed),
                monitor, profile);
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
            e.printStackTrace();
        }
        return input;
    }

    protected KeyAst.File getParseContext() {
        if (ctx == null) {
            try {
                ctx = ParsingFacade.parseFile(file.getCharStream());
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
        }
        return ctx;
    }

    protected ProofSettings getPreferences() throws ProofInputException {
        if (initConfig.getSettings() == null) {
            return readPreferences();
        } else {
            return initConfig.getSettings();
        }
    }

    public ProofSettings readPreferences() throws ProofInputException {
        if (file.isDirectory()) {
            return null;
        }
        var ctx = getParseContext();
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
                var ctx = getParseContext();
                includes = ctx.getIncludes(file.file().getParentFile().toURI().toURL());
            } catch (Exception e) {
                throw new ProofInputException(e);
            }
        }
        return includes;
    }


    @Override
    public File readBootClassPath() {
        var pi = getProblemInformation();
        String bootClassPath = pi.getBootClassPath();
        if (bootClassPath == null) return null;
        File bootClassPathFile = new File(bootClassPath);
        if (!bootClassPathFile.isAbsolute()) {
            // convert to absolute by resolving against the parent path of the parsed file
            String parentDirectory = file.file().getParent();
            bootClassPathFile = new File(parentDirectory, bootClassPath);
        }

        return bootClassPathFile;
    }

    protected @NotNull ProblemInformation getProblemInformation() {
        if (problemInformation == null) {
            var ctx = getParseContext();
            problemInformation = ctx.getProblemInformation();
        }
        return problemInformation;
    }


    @NotNull
    @Override
    public List<@NotNull File> readClassPath() {
        var pi = getProblemInformation();
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
        var pi = getProblemInformation();
        String javaPath = pi.getJavaSource();
        if (javaPath != null) {
            File absFile = new File(javaPath);
            if (!absFile.isAbsolute()) {
                // convert to absolute by resolving against the parent path of the parsed file
                File parent = file.file().getParentFile();
                absFile = new File(parent, javaPath);
            }
            if (!absFile.exists()) {
                throw new ProofInputException(String.format("Declared Java source %s not found.", javaPath));
            }
            return absFile.getAbsolutePath();
        }
        return javaPath;
    }


    @Override
    public ImmutableSet<PositionedString> read() throws ProofInputException {
        ImmutableSet<PositionedString> warnings = DefaultImmutableSet.nil();
        if (initConfig == null) {
            throw new IllegalStateException("KeYFile: InitConfig not set.");
        }

        //read .key file
        Debug.out("Reading KeY file", file);
        var ci = getParseContext().getChoices();
        initConfig.addCategory2DefaultChoices(ci.getDefaultOptions());

        readSorts();
        readFuncAndPred();
        readRules();
        SpecificationRepository specRepos
                = initConfig.getServices().getSpecificationRepository();
        var cinvs = new ContractsAndInvariantsFinder(initConfig.getServices(), initConfig.namespaces());
        getParseContext().accept(cinvs);
        specRepos.addContracts(ImmutableSet.fromCollection(cinvs.getContracts()));
        specRepos.addClassInvariants(ImmutableSet.fromCollection(cinvs.getInvariants()));
        Debug.out("Read KeY file   ", file);
        return warnings;
    }

    @NotNull
    protected ProblemFinder getProblemFinder() {
        if (problemFinder == null) {
            problemFinder = new ProblemFinder(initConfig.getServices(), initConfig.namespaces());
            getParseContext().accept(problemFinder);
        }
        return problemFinder;
    }


    /**
     * reads the sorts declaration of the .key file only,
     * modifying the sort namespace
     * of the initial configuration
     */
    public void readSorts() throws ProofInputException {
        var ctx = getParseContext();
        KeyIO io = new KeyIO(initConfig.getServices(), initConfig.namespaces());
        io.evalDeclarations(ctx);
        var choice = getParseContext().getChoices();
        //we ignore the namespace of choice finder.
        initConfig.addCategory2DefaultChoices(choice.getDefaultOptions());
    }


    /**
     * reads the functions and predicates declared in the .key file only,
     * modifying the function namespaces of the respective taclet options.
     */
    public void readFuncAndPred() throws ProofInputException {
        if (file == null) return;
        var ctx = getParseContext();
        KeyIO io = new KeyIO(initConfig.getServices(), initConfig.namespaces());
        io.evalFuncAndPred(ctx);
    }


    /**
     * reads the rules and problems declared in the .key file only,
     * modifying the set of rules
     * of the initial configuration
     */
    public void readRules() throws ProofInputException {
        KeyIO io = new KeyIO(initConfig.getServices(), initConfig.namespaces());
        var ctx = getParseContext();
        var visitor = new TacletPBuilder(initConfig.getServices(), initConfig.namespaces(),
                initConfig.getTaclet2Builder());
        ctx.accept(visitor);
        var taclets = visitor.getTopLevelTaclets();
        //System.out.format("Found taclets (%s): %d%n", file, taclets.size());
        initConfig.addTaclets(taclets);
    }


    public void close() {
        ctx = null;
        problemFinder = null;
        problemInformation = null;
    }


    public String chooseContract() {
        return null;
    }

    public String getProofObligation() {
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