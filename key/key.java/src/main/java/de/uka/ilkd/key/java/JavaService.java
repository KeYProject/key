package de.uka.ilkd.key.java;

import com.github.javaparser.Position;
import com.github.javaparser.*;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.comments.CommentsCollection;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.VoidType;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.*;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.FieldSpecification;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.transformations.KeYJavaPipeline;
import de.uka.ilkd.key.java.transformations.pipeline.ConstantStringExpressionEvaluator;
import de.uka.ilkd.key.java.transformations.pipeline.TransformationPipelineServices;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.proof.io.consistency.FileRepo;
import de.uka.ilkd.key.util.LinkedHashMap;
import de.uka.ilkd.key.util.*;
import de.uka.ilkd.key.util.parsing.BuildingExceptions;
import de.uka.ilkd.key.util.parsing.BuildingIssue;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.io.*;
import java.net.MalformedURLException;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Facade for the JavaParser.
 * <p>
 * This class allows you to configure a classpath, and source path.
 * To parse Java source files, to process them in the Java2Java pipeline
 * and to have a proper symbol resolution.
 *
 * @author Alexander Weigl
 * @version 1 (19.02.22)
 */
public class JavaService {
    private static final Logger LOGGER = LoggerFactory.getLogger(JavaService.class);
    private Namespace<SchemaVariable> schemaVariables;

    /**
     * the File object that describes the directory from which the internal
     * classes are to be read. They are read in differently - therefore the
     * second category. A null value indicates that the boot classes are to
     * be read from an internal repository.
     */
    private File bootClassPath;

    /**
     * this mapping stores the relation between recoder and KeY entities in a
     * bidirectional way.
     * <p>
     * It is used for syntactical structures and types.
     */
    private final KeYJPMapping mapping = new KeYJPMapping();

    /**
     * Counter used to enumerate the anonymous implicit classes used in parsing of Java Fragments
     */
    private static AtomicInteger interactCounter = new AtomicInteger();

    /**
     * This flag indicates whether we are currently parsing library classes
     * (special classes)
     */
    private boolean parsingLibs = false;

    /**
     * the object that handles the transformation from recoder AST to KeY AST
     */
    private final JP2KeYConverter converter;

    /**
     * the object that handles the transformation from recoder types to KeY
     * types
     */
    private final JP2KeYTypeConverter typeConverter;

    /**
     * The list of dynamical created {@link CompilationUnit}s
     * that contain the classes that are referenced but not defined. For those class types
     * a dummy stub is created at parse time.
     */
    private Collection<? extends CompilationUnit> dynamicallyCreatedCompilationUnits;


    private final CompilationUnit compilationUnitOfVirtualClasses;

    private final Services services;
    private final JavaParserFactory programFactory;


    /**
     * return the associated converter object
     *
     * @return not null
     */
    public JP2KeYConverter getConverter() {
        return converter;
    }

    /**
     * return the associated type converter object
     *
     * @return not null
     */
    public JP2KeYTypeConverter getTypeConverter() {
        return typeConverter;
    }

    /**
     * set this to true before parsing special classes and to false afterwards.
     *
     * @param v the state of the special parsing flage
     */
    private void setParsingLibs(boolean v) {
        parsingLibs = v;
    }

    /**
     * are we currently parsing library code (special classes)?
     *
     * @return true iff currently parsing special classes.
     */
    public boolean isParsingLibs() {
        return parsingLibs;
    }

    public KeYJPMapping rec2key() {
        return mapping;
    }

    private void insertToMap(Node r, ModelElement k) {
        if (r != null && k != null) {
            rec2key().put(r, k);
        } else {
            LOGGER.debug("Rec2Key.insertToMap: Omitting entry  (r = {}  -> k =  {})", r, k);
        }
    }

    //region parsing of compilation units

    /**
     * parse a list of java files and transform it to the corresponding KeY
     * entities.
     * <p>
     * Each element of the array is treated as a filename to read in.
     *
     * @param cUnitStrings a list of strings, each element is interpreted as a file to be
     *                     read. not null.
     * @param fileRepo     the fileRepo which will store the files
     * @return a new list containing the recoder compilation units corresponding
     * to the given files.
     * @throws ParseExceptionInFile any exception occurring while treating the file is wrapped
     *                              into a parse exception that contains the filename.
     */

    public List<de.uka.ilkd.key.java.CompilationUnit> readCompilationUnitsAsFiles(List<String> cUnitStrings, FileRepo fileRepo)
            throws ParseExceptionInFile {

        List<CompilationUnit> cUnits = recoderCompilationUnitsAsFiles(cUnitStrings, fileRepo);
        var result = new ArrayList<de.uka.ilkd.key.java.CompilationUnit>(cUnits.size());
        for (CompilationUnit cu : cUnits) {
            try {
                result.add(getConverter().processCompilationUnit(cu));
            } catch (Exception e) {
                throw new ParseExceptionInFile("", e); //Find a better solution
            }
        }
        return result;
    }


    /**
     * parse a list of java files.
     * <p>
     * Each element of the array is treated as a filename to read in.
     *
     * @param filenames a list of strings, each element is interpreted as a file to be
     *                  read. not null.
     * @param fileRepo  the fileRepo which will store the files
     * @return a new list containing the recoder compilation units corresponding
     * to the given files.
     */
    private List<CompilationUnit> recoderCompilationUnitsAsFiles(List<String> filenames, FileRepo fileRepo)
            throws BuildingExceptions {
        List<CompilationUnit> cUnits = new ArrayList<>();
        parseSpecialClasses(fileRepo);
        var result = filenames.stream().parallel().map(it -> parseCompilationUnit(it, fileRepo))
                .collect(Collectors.toList());

        if (result.stream().anyMatch(it -> !it.isSuccessful())) {
            var problems = result.stream().flatMap(it -> it.getProblems().stream());
            reportErrors(problems);
        }
        // transform program
        transformModel(cUnits);
        return result.stream().map(it -> it.getResult().get()).collect(Collectors.toList());
    }

    private <T> void reportErrors(ParseResult<T> result) {
        if (!result.isSuccessful()) {
            reportErrors(result.getProblems().stream());
        }
    }

    private <T> void reportErrors(List<ParseResult<T>> result) {
        if (result.stream().anyMatch(it -> !it.isSuccessful())) {
            reportErrors(result.stream().flatMap(it -> it.getProblems().stream()));
        }
    }


    private void reportErrors(Stream<Problem> problems) {
        var be = problems.map(it -> {
            var loc = it.getLocation()
                    .flatMap(TokenRange::toRange)
                    .map(b -> b.begin)
                    .orElse(new Position(-1, -1));
            return new BuildingIssue(it.getVerboseMessage(),
                    null, false, loc.line, loc.column, -1, -1, null /*TODO*/);
        }).collect(Collectors.toList());
        throw new BuildingExceptions(be);
    }

    private ParseResult<CompilationUnit> parseCompilationUnit(String filename, @Nullable FileRepo fileRepo) {
        try {
            Reader is;
            if (fileRepo != null)
                is = new InputStreamReader(fileRepo.getInputStream(Paths.get(filename)));
            else
                is = new FileReader(filename);
            try (BufferedReader br = new BufferedReader(is)) {
                ParseResult<CompilationUnit> cu = getProgramFactory().parseCompilationUnit(br);
                if (cu.getResult().isPresent()) {
                    cu.getResult().get().setStorage(Paths.get(filename));
                }
                return cu;
            }

        } catch (FileNotFoundException e) {
            return new ParseResult<>(null,
                    Collections.singletonList(new Problem("Could not find " + filename, null, e)), new CommentsCollection());
        } catch (IOException e) {
            return new ParseResult<>(null,
                    Collections.singletonList(new Problem("I/O error reading: " + filename, null, e)), new CommentsCollection());
        }
    }

    /**
     * read a compilation unit, given as a string.
     *
     * @param cUnitString a string represents a compilation unit
     * @return a KeY structured compilation unit.
     */
    public de.uka.ilkd.key.java.CompilationUnit readCompilationUnit(String cUnitString) {
        var cc = recoderCompilationUnits(Collections.singletonList(cUnitString));
        var cu = cc.get(0);
        return (de.uka.ilkd.key.java.CompilationUnit) getConverter().process(cu);
    }

    /**
     * read a number of compilation units, each given as a string.
     *
     * @param cUnitStrings an array of strings, each element represents a compilation
     *                     unit
     * @return a list of KeY structured compilation units.
     */
    List<CompilationUnit> recoderCompilationUnits(List<String> cUnitStrings) {
        parseSpecialClasses();
        var cUnits = cUnitStrings.parallelStream()
                .map(it -> {
                    LOGGER.debug("Reading {}", trim(it));
                    var sr = new StringReader(it);
                    return getProgramFactory().parseCompilationUnit(sr);
                }).collect(Collectors.toList());

        if (cUnits.stream().anyMatch(it -> !it.isSuccessful())) {
            reportErrors(cUnits.stream().flatMap(it -> it.getProblems().stream()));
        }

        // transform program
        final var collect = cUnits.stream().map(it -> it.getResult().get()).collect(Collectors.toList());
        transformModel(collect);
        return collect;
    }

    // ----- parsing libraries

    public void setClassPath(File bootClassPath, List<Path> classPath) {
        this.sourcePaths.clear();
        this.sourcePaths.addAll(classPath);
        this.bootClassPath = bootClassPath;
        typeSolver = null;
    }

    /**
     * get the list of names of classes that have been created dynamically due
     * to lacking definitions.
     * <p>
     * For all classes that are referenced but not defined, an empty dummy stub
     * is created. This method returns the list of their fully qualified class
     * names.
     *
     * @return an unmodifiable list of fully qualified class names
     * @author mu, on rb's specification ;)
     */
    public List<String> getDynamicallyCreatedClasses() {
        List<String> ret = new ArrayList<>();
        if (dynamicallyCreatedCompilationUnits != null) {
            for (CompilationUnit cu : dynamicallyCreatedCompilationUnits) {
                final var pt = cu.getPrimaryTypeName();
                pt.ifPresent(ret::add);
            }
        }
        return ret;
    }

    /**
     * This method loads the internal classes - also called the "boot" classes.
     * <p>
     * If {@link #bootClassPath} is set to null, it locates java classes that
     * are stored internally within the jar-file or the binary directory. The
     * JAVALANG.TXT file lists all files to be loaded. The files are found using
     * a special {@link JavaReduxFileCollection}.
     * <p>
     * If, however, {@link #bootClassPath} is assigned a value, this is treated
     * as a directory (not a JAR file at the moment) and all files in this
     * directory are read in. This is done using a
     * {@link DirectoryFileCollection}.
     *
     * @param fileRepo the FileRepo that provides the InputStream to resources
     * @return
     */
    private List<CompilationUnit> parseInternalClasses(FileRepo fileRepo) throws IOException {
        Stream<URL> paths;

        if (bootClassPath == null) {
            var bootCollection = new JavaReduxFileCollection(services.getProfile());
            paths = bootCollection.getResources();
        } else {
            paths = Files.walk(bootClassPath.toPath())
                    .filter(it -> it.getFileName().endsWith(".java") || it.getFileName().endsWith(".jml"))
                    .map(it -> {
                        try {
                            return it.toUri().toURL();
                        } catch (MalformedURLException e) {
                            e.printStackTrace();
                        }
                        return null;
                    });
        }

        var seq = paths.parallel().map(it -> {
            try {
                final var inputStream = fileRepo == null ? it.openStream() : fileRepo.getInputStream(it);
                try (Reader f = new BufferedReader(new InputStreamReader(inputStream))) {
                    return getProgramFactory().parseCompilationUnit(f);
                }
                //Set storage location?
            } catch (IOException e) {
                e.printStackTrace();
            }
            return null;
        }).collect(Collectors.toList());

        if (seq.stream().anyMatch(it -> !it.isSuccessful())) {
            reportErrors(seq.stream().flatMap(it -> it.getProblems().stream()));
        }

        return seq.stream().map(it -> it.getResult().get()).collect(Collectors.toList());
    }

    /**
     * reads compilation units that will be treated as library classes.
     * <p>
     * Proceed as follows:
     *
     * <ol>
     * <li> If "classPath" is set and contains at least one entry
     * <ol>
     * <li>read every <code>.java</code> file within the entries (directories
     * or zip files)
     * <li>read every <code>.class</code> file within the entries
     * (directories or zip files)
     * </ol>
     * <li>else read a special collection of classes that is stored internally
     * </ol>
     *
     * @param fileRepo the FileRepo for obtaining InputStreams
     * @throws IOException
     * @author mulbrich
     */
    private List<CompilationUnit> parseLibs(FileRepo fileRepo) throws IOException {

        var internal = parseInternalClasses(fileRepo);
        List<FileCollection> sources = new ArrayList<>();
        List<CompilationUnit> rcuList = new ArrayList<>(internal);

        for (var cp : sourcePaths) {
            if (Files.isDirectory(cp)) {
                sources.add(new DirectoryFileCollection(cp.toFile()));
            } else {
                sources.add(new ZipFileCollection(cp.toFile()));
            }
        }

        /* While the resources are read (and possibly copied) via the FileRepo, the data location
         * is left as it is. This leaves the line information intact. */
        Path currentDataLocation;

        // -- read jml files --
        for (FileCollection fc : sources) {
            FileCollection.Walker walker = fc.createWalker(".jml");
            while (walker.step()) {
                currentDataLocation = walker.getCurrentLocation();
                try (InputStream is = walker.openCurrent(fileRepo);
                     Reader isr = new InputStreamReader(is);
                     Reader f = new BufferedReader(isr)) {
                    var rcu = getProgramFactory().parseCompilationUnit(f);
                    reportErrors(rcu);
                    var cu = rcu.getResult().get();
                    cu.setStorage(currentDataLocation);
                    removeCodeFromClasses(cu, false);
                    rcuList.add(cu);
                }
            }
        }

        // -- read java files --
        for (FileCollection fc : sources) {
            FileCollection.Walker walker = fc.createWalker(".java");
            while (walker.step()) {
                currentDataLocation = walker.getCurrentLocation();
                try (InputStream is = walker.openCurrent(fileRepo);
                     Reader isr = new InputStreamReader(is);
                     Reader f = new BufferedReader(isr)) {
                    var rcu = getProgramFactory().parseCompilationUnit(f);
                    reportErrors(rcu);
                    var cu = rcu.getResult().get();
                    cu.setStorage(currentDataLocation);
                    removeCodeFromClasses(cu, true);
                    rcuList.add(cu);
                }
            }
        }

        // -- read class files --
        /*
        ClassFileDeclarationManager manager = new ClassFileDeclarationManager(pf);
        ByteCodeParser parser = new ByteCodeParser();
        for (FileCollection fc : sources) {
            FileCollection.Walker walker = fc.createWalker(".class");
            while (walker.step()) {
                currentDataLocation = walker.getCurrentDataLocation();
                try (InputStream is = new BufferedInputStream(walker.openCurrent(fileRepo))) {
                    ClassFile cf = parser.parseClassFile(is);
                    manager.addClassFile(cf, currentDataLocation);
                } catch (Exception ex) {
                    throw new ConvertException("Error while loading: " + walker.getCurrentDataLocation(), ex);
                }
            }
        }
        rcuList.addAll(manager.getCompilationUnits());
        */

        var rcu = getProgramFactory().parseCompilationUnit(
                new StringReader("public class " + JavaInfo.DEFAULT_EXECUTION_CONTEXT_CLASS +
                        " { public static void " + JavaInfo.DEFAULT_EXECUTION_CONTEXT_METHOD + "() {}  }"));
        reportErrors(rcu);
        rcuList.add(rcu.getResult().get());
        return rcuList;
    }

    /*
     * removes code from a parsed compilation unit. This includes method bodies,
     * initial assignments, compile-time constants, static blocks.
     *
     * This is done for classes that are read in a classpath-context. For these
     * classes only contracts (if present) are to be considered.
     *
     * No need to inform changeHistory since the class is not yet registered.
     * Method bodies are set to null, i.e. all methods are stubs only
     *
     * TODO remove jml-model methods (or similar) also?
     * FIXME this does not work if jml set statements are last in a method
     * TODO leave it out all together?
     */
    private void removeCodeFromClasses(CompilationUnit rcu, boolean allowed) {
        VoidVisitor<Void> removeBodies = new VoidVisitorAdapter<>() {
            @Override
            public void visit(MethodDeclaration n, Void arg) {
                if (!allowed && n.getBody() != null) {
                    LOGGER.warn("Method body ({}) should not be allowed: {}", n.getNameAsString(), rcu.getStorage());
                }
                n.setBody(null);
            }
        };
        rcu.accept(removeBodies, null);
    }

    /**
     * makes sure that the special classes (library classes) have been parsed
     * in.
     * <p>
     * If not parsed yet, the special classes are read in and converted.
     * This method throws only runtime exceptions for historical reasons.
     */
    public void parseSpecialClasses() {
        parseLibraryClasses0(null);
    }

    /**
     * makes sure that the special classes (library classes) have been parsed
     * in.
     * <p>
     * If not parsed yet, the special classes are read in and converted.
     * This method throws only runtime exceptions for historical reasons.
     *
     * @param fileRepo the fileRepo which will store the files
     */
    public void parseSpecialClasses(FileRepo fileRepo) {
        try {
            parseLibraryClasses0(fileRepo);
        } catch (Exception e) {
            reportError("An error occurred while parsing the libraries", e);
        }
    }

    private void parseLibraryClasses0(FileRepo fileRepo) {
        if (mapping.parsedSpecial()) {
            return;
        }
        // go to special mode -> used by the converter!
        setParsingLibs(true);

        try {
            List<CompilationUnit> specialClasses = parseLibs(fileRepo);
        /*
        dynamicallyCreatedCompilationUnits = keySourceInfo.getCreatedStubClasses();
        specialClasses.addAll(dynamicallyCreatedCompilationUnits);
        keySourceInfo.setIgnoreUnresolvedClasses(false);
        changeHistory.updateModel();
        */
            transformModel(specialClasses);

            // make them available to the rec2key mapping
            for (CompilationUnit cu : specialClasses) {
                var dl = cu.getStorage();
                if (dl.isEmpty()) throw new AssertionError("DataLocation not set on compilation unit");
                getConverter().processCompilationUnit(cu);
            }

            /* TODO weigl
            // Ensure that rec2key is complete (at least the NullType needs to be available!)
            if (!rec2key().mapped(getNameInfo().getNullType())) {
                Sort objectSort = services.getNamespaces().sorts().lookup(new Name("java.lang.Object"));
                assert objectSort != null;
                NullSort nullSort = new NullSort(objectSort);
                KeYJavaType result = new KeYJavaType(NullType.JAVA_NULL, nullSort);
                if (services.getNamespaces().sorts().lookup(nullSort.name()) == null) {
                    services.getNamespaces().sorts().add(nullSort);
                }
                rec2key().put(servConf.getNameInfo().getNullType(), result);
            }
            */

        } catch (IOException e) {
            e.printStackTrace();
        }

        // tell the mapping that we have parsed the special classes
        rec2key().parsedSpecial(true);

        setParsingLibs(false);
    }

    /**
     * Transform a list of compilation units.
     * <p>
     * Once a compilation unit has been parsed in and prior to converting it to
     * the KeY structures, several transformations have to be performed upon it.
     * <p>
     * You can add your own Transformation here. Make sure it is in the correct
     * order.
     *
     * @param cUnits a list of compilation units, not null.
     */

    protected void transformModel(List<CompilationUnit> cUnits) {
        KeYJavaPipeline pipeline = KeYJavaPipeline.createDefault(createPipelineServices(cUnits));
        pipeline.apply();
    }


    // ----- methods dealing with blocks.

    /**
     * wraps a RECODER StatementBlock in a method
     * <p>
     * it is wrapped in a method called
     * <code>&lt;virtual_method_for_parsing&gt;</code>.
     *
     * @param block the StatementBlock to wrap
     * @return the enclosing MethodDeclaration
     */
    protected MethodDeclaration embedBlock(BlockStmt block) {
        MethodDeclaration mdecl = new MethodDeclaration(new NodeList<>(), new VoidType(),
                "$virtual_method_for_parsing");
        mdecl.setBody(block);
        return mdecl;
    }

    /**
     * wraps a RECODER MethodDeclaration in a class
     *
     * @param mdecl   the declaration.MethodDeclaration to wrap
     * @param context the declaration.ClassDeclaration where the method
     *                has to be embedded
     * @return the enclosing declaration.ClassDeclaration
     */
    protected ClassOrInterfaceDeclaration embedMethod(MethodDeclaration mdecl, JPContext context) {
        ClassOrInterfaceDeclaration classContext = context.getClassDeclaration();
        classContext.addMember(mdecl);
        /*for (int i = 0, sz = memberList.size(); i < sz; i++) {
            if (memberList.get(i) instanceof MethodDeclaration) {
                MethodDeclaration olddecl =
                        (MethodDeclaration) memberList.get(i);
                if (olddecl.getName().equals(mdecl.getName())) {
                    memberList.remove(i);
                }
            }
        }*/
        return classContext;
    }

    /**
     * creates an empty RECODER compilation unit with a temporary name.
     *
     * @return the new CompilationUnit
     */
    public JPContext createEmptyContext() {
        var classContext = interactClassDecl();
        var cu = new CompilationUnit(null, new NodeList<>(), new NodeList<>(classContext), null);
        getSymbolResolver().inject(cu);
        return new JPContext(cu, classContext);
    }

    /**
     * create a new Context with a temporary name and make a list of variables
     * visible from within.
     *
     * @param vars a list of variables
     * @param csi  a special source info
     * @return a newly created context.
     */
    protected JPContext createContext(ImmutableList<ProgramVariable> vars) {
        var classContext = interactClassDecl();
        addProgramVariablesToClassContext(classContext, vars);
        var cu = new CompilationUnit(null, new NodeList<>(), new NodeList<>(classContext), null);
        getSymbolResolver().inject(cu);
        return new JPContext(cu, classContext);
    }

    /**
     * add a list of variables to a context
     *
     * @param classContext context to add to
     * @param vars         vars to add
     */
    private void addProgramVariablesToClassContext(ClassOrInterfaceDeclaration classContext,
                                                   ImmutableList<ProgramVariable> vars) {
        Map<String, VariableDeclarator> names2var = new LinkedHashMap<>();
        Set<String> names = new HashSet<>();

        for (ProgramVariable var : vars) {
            if (names.contains(var.name().toString())) {
                continue;
            }
            VariableSpecification keyVarSpec = lookupVarSpec(var);
            names.add(var.name().toString());
            if (keyVarSpec == null) {
                keyVarSpec = new FieldSpecification(var);
            }

            if (var.getKeYJavaType() == null) {
                /// The program variable "variant" introduced to prove loop termination has sort
                /// "any" and, hence, no type. Parsing modalities fails on branches on which the
                /// variable exists. Therefore, it seems better to silently ignore such program
                /// variables (not making themaccessible) rather than to throw an exception.
                /// MU 01.2019
                // throw new IllegalArgumentException("Variable " + var + " has no type");
                continue;
            }

            Type javaType = var.getKeYJavaType().getJavaType();
            if (javaType == null) continue;
            String typeName = javaType.getFullName();


            FieldDeclaration recVar = new FieldDeclaration(new NodeList<>(),
                    new VariableDeclarator(name2typeReference(typeName), keyVarSpec.getName()));

            classContext.addMember(recVar);
            var rvarspec = recVar.getVariables().get(0);
            names2var.put(var.name().toString(), rvarspec);
            insertToMap(recVar.getVariables().get(0), keyVarSpec);
        }
    }

    /**
     * look up in the mapping the variable specification for a program variable.
     * <p>
     * used by addProgramVariablesToClassContext
     */
    private VariableSpecification lookupVarSpec(ProgramVariable pv) {
        for (final Object o : mapping.elemsKeY()) {
            if ((o instanceof VariableSpecification) && ((VariableSpecification) o).getProgramVariable() == pv) {
                return (VariableSpecification) o;
            }
        }
        return null;
    }

    /**
     * given a name as string, construct a recoder type reference from it.
     *
     * @param typeName non-null type name as string
     * @return a freshly created type reference to the given type.
     */
    private com.github.javaparser.ast.type.Type name2typeReference(String typeName) {
        return new ClassOrInterfaceType(null, typeName);

        /*PackageReference pr = null;
        String baseType = TypeNameTranslator.getBaseType(typeName);
        int idx = baseType.indexOf('.');
        int lastIndex = 0;
        String anonType = "";
        while (idx != -1 && baseType.charAt(lastIndex) >= 'a'
                && baseType.charAt(lastIndex) <= 'z') {
            String s = baseType.substring(lastIndex, idx);
            pr = new PackageReference(pr, new Identifier(s));
            lastIndex = idx + 1;
            idx = baseType.indexOf('.', lastIndex);
        }
        baseType = anonType + baseType;
        Identifier typeId;
        if (baseType.charAt(0) == '<') {
            typeId = new ImplicitIdentifier(baseType.substring(lastIndex));
        } else {
            typeId = new ObjectTypeIdentifier(baseType.substring(lastIndex));
        }
        TypeReference result = new TypeReference(pr, typeId);
        result.setDimensions(TypeNameTranslator.getDimensions(typeName));
        return result;
         */
    }

    /**
     * parses a given JavaBlock using the context to determine the right
     * references and returns a statement block of recoder.
     *
     * @param block   a String describing a java block
     * @param context CompilationUnit in which the block has to be
     *                interpreted
     * @return the parsed and resolved recoder statement block
     */
    BlockStmt recoderBlock(String block, JPContext context) {
        parseSpecialClasses();
        var bl = getProgramFactory().parseStatementBlock(block);
        if (!bl.isSuccessful()) {
            reportErrors(bl);
        }
        final var blockStmt = bl.getResult().get();
        embedMethod(embedBlock(blockStmt), context);
        // normalise constant string expressions
        List<CompilationUnit> cunits = new ArrayList<>();
        cunits.add(context.getCompilationUnitContext());
        new ConstantStringExpressionEvaluator(createPipelineServices()).apply(context.getClassDeclaration());
        return blockStmt;
    }

    private TransformationPipelineServices createPipelineServices() {
        return createPipelineServices(new ArrayList<>(0));
    }

    private TransformationPipelineServices createPipelineServices(List<CompilationUnit> cUnits) {
        TransformationPipelineServices.TransformerCache cache = new TransformationPipelineServices.TransformerCache(cUnits);
        return new TransformationPipelineServices(this, cache);
    }


    /**
     * parses a given JavaBlock using the context to determine the right
     * references
     *
     * @param block   a String describing a java block
     * @param context CompilationUnit in which the block has to be
     *                interprested
     * @return the parsed and resolved JavaBlock
     */
    public JavaBlock readBlock(String block, JPContext context) {
        var sb = recoderBlock(block, context);
        return JavaBlock.createJavaBlock((StatementBlock) getConverter().process(sb));
    }

    /**
     * parses a given JavaBlock using the context to determine the right
     * references using an empty context
     *
     * @param block a String describing a java block
     * @return the parsed and resolved JavaBlock
     */
    public JavaBlock readBlockWithEmptyContext(String block) {
        return readBlock(block, createEmptyContext());
    }

    /**
     * parses a given JavaBlock using a namespace to determine the right
     * references using an empty context. The variables of the namespace are
     * used to create a new class context
     *
     * @param s a String describing a java block
     * @return the parsed and resolved JavaBlock
     */
    public JavaBlock readBlockWithProgramVariables(Namespace<IProgramVariable> variables, String s) {
        ImmutableList<ProgramVariable> pvs = ImmutableSLList.nil();
        for (IProgramVariable n : variables.allElements()) {
            if (n instanceof ProgramVariable) {
                pvs = pvs.append((ProgramVariable) n); //preserve the order (nested namespaces!)
            }
        }
        return readBlock(s, createContext(pvs));
    }

    /**
     * make a new classdeclaration with a temporary name.
     * <p>
     * The name is a unique implicit identifier.
     *
     * @return a newly created recoder ClassDeclaration with a unique name
     */
    private ClassOrInterfaceDeclaration interactClassDecl() {
        var classContext = new ClassOrInterfaceDeclaration(new NodeList<>(), false,
                "$virtual_class_for_parsing" + interactCounter.incrementAndGet());
        return classContext;
    }

    // ----- helpers

    /**
     * reduce the size of a string to a maximum of 150 characters. Introduces
     * ellipses [...]
     */
    private static String trim(String s) {
        return trim(s, 150);
    }

    /**
     * reduce the size of a string to a maximum of length.
     */
    private static String trim(String s, int length) {
        if (s.length() > length)
            return s.substring(0, length - 5) + "[...]";
        return s;
    }

    // ----- error handling

    /**
     * tries to parse recoders exception position information
     */
    private static int[] extractPositionInfo(String errorMessage) {
        if (errorMessage == null || errorMessage.indexOf('@') == -1) {
            return new int[0];
        }
        int line = -1;
        int column = -1;
        try {
            String pos = errorMessage.substring(errorMessage.indexOf("@") + 1);
            pos = pos.substring(0, pos.indexOf(" "));
            line = Integer.parseInt(pos.substring(0, pos.indexOf('/')));
            column = Integer.parseInt(pos.substring(pos.indexOf('/') + 1));
        } catch (NumberFormatException nfe) {
            LOGGER.debug("recoder2key:unresolved reference at " + "line:" + line + " column:" + column);
            return new int[0];
        } catch (StringIndexOutOfBoundsException siexc) {
            return new int[0];
        }
        return new int[]{line, column};
    }

    /**
     * report an error in form of a ConvertException. The cause is always
     * attached to the resulting exception.
     *
     * @param message message to be used.
     * @param t       the cause of the exceptional case
     * @throws ConvertException always
     */
    public static void reportError(String message, Throwable t) {
        // Attention: this highly depends on Recoders exception messages!
        Throwable cause = t;
        if (t instanceof ExceptionHandlerException && t.getCause() != null) {
            cause = t.getCause();
        }

        if (cause instanceof PosConvertException) {
            throw (PosConvertException) cause;
        }

        int[] pos = extractPositionInfo(cause.toString());
        final RuntimeException rte;
        if (pos.length > 0) {
            rte = new PosConvertException(message, pos[0], pos[1]);
            rte.initCause(cause);
        } else {
            rte = new ConvertException(message, cause);
        }

        throw rte;
    }


    /**
     * A list of {@link File} objects that describes the classpath to be searched
     * for classes or Java files.
     */
    @Nonnull
    private final List<Path> sourcePaths;

    @Nullable
    private ParserConfiguration config;

    @Nullable
    private TypeSolver typeSolver;

    @Nullable
    private JavaSymbolSolver symbolResolver;

    private boolean useSystemClassLoaderInResolution;

    public JavaService(Services services, Collection<Path> sourcePaths) {
        this.services = services;
        this.sourcePaths = new ArrayList<>(sourcePaths);
        converter = new JP2KeYConverter(services, mapping, schemaVariables);
        typeConverter = new JP2KeYTypeConverter(services);
        programFactory = new JavaParserFactory(this);
        compilationUnitOfVirtualClasses = null;
    }

    public JavaParser createJavaParser() {
        return new JavaParser(getConfiguration());
    }

    @Nonnull
    private ParserConfiguration getConfiguration() {
        if (config == null) {
            config = new ParserConfiguration();
        }
        config.setSymbolResolver(getSymbolResolver());
        return config;
    }

    @Nonnull
    private JavaSymbolSolver getSymbolResolver() {
        if (symbolResolver == null) {
            symbolResolver = new JavaSymbolSolver(getTypeSolver());
        }
        return symbolResolver;
    }


    public TypeSolver getTypeSolver() {
        if (typeSolver == null) {
            var ct = new CombinedTypeSolver();
            for (var sourcePath : sourcePaths) {
                if (Files.isRegularFile(sourcePath)) {
                    if (sourcePath.getFileName().endsWith(".jar")) {
                        try {
                            ct.add(new JarTypeSolver(sourcePath));
                        } catch (IOException e) {
                            LOGGER.error(e.getMessage(), e);
                        }
                    } else {
                        /*sourcePath.getRoot();
                        final Matcher matcher = IOUtil.URL_JAR_FILE.matcher();
                        if (matcher.matches()) {
                         */
                        //TODO add support for java files inside
                    }
                } else if (Files.isDirectory(sourcePath)) {
                    ct.add(new JavaParserTypeSolver(sourcePath, config));
                }
            }

            if (useSystemClassLoaderInResolution) {
                ct.add(new ReflectionTypeSolver(true));
            }

            typeSolver = ct;
        }
        return typeSolver;
    }

    /**
     * If set to true the symbol solver do not use the {@link ClassLoaderTypeSolver} with the system class class loader.
     * This means, that classes defined by the JRE are not found, if they are not given in the class path.
     * In particular, only JavaRedux and Red classes (if added) are
     * <p>
     * the next parser runs
     *
     * @param useSystemClassLoaderInResolution
     */
    public void setUseSystemClassLoaderInResolution(boolean useSystemClassLoaderInResolution) {
        this.useSystemClassLoaderInResolution = useSystemClassLoaderInResolution;
        typeSolver = null;
    }

    public JavaParserFactory getProgramFactory() {
        return programFactory;
    }
}