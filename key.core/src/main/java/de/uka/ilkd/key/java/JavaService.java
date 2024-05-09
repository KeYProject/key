/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java;

import java.io.*;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.*;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.BiFunction;
import java.util.stream.Collectors;

import de.uka.ilkd.key.java.ast.StatementBlock;
import de.uka.ilkd.key.java.ast.TypeScope;
import de.uka.ilkd.key.java.ast.abstraction.Type;
import de.uka.ilkd.key.java.ast.declaration.FieldSpecification;
import de.uka.ilkd.key.java.ast.declaration.Modifier;
import de.uka.ilkd.key.java.ast.declaration.VariableSpecification;
import de.uka.ilkd.key.java.ast.reference.TypeRef;
import de.uka.ilkd.key.java.loader.*;
import de.uka.ilkd.key.java.transformations.KeYJavaPipeline;
import de.uka.ilkd.key.java.transformations.pipeline.ConstantStringExpressionEvaluator;
import de.uka.ilkd.key.java.transformations.pipeline.TransformationPipelineServices;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.proof.io.consistency.FileRepo;
import de.uka.ilkd.key.util.DirectoryFileCollection;
import de.uka.ilkd.key.util.FileCollection;
import de.uka.ilkd.key.util.ZipFileCollection;
import de.uka.ilkd.key.util.parsing.BuildingExceptions;
import de.uka.ilkd.key.util.parsing.BuildingIssue;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.Pair;

import com.github.javaparser.*;
import com.github.javaparser.Position;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.key.sv.KeyContextStatementBlock;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.ast.type.VoidType;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.model.typesystem.NullType;
import com.github.javaparser.resolution.types.ResolvedPrimitiveType;
import com.github.javaparser.resolution.types.ResolvedVoidType;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

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

    /**
     * this mapping stores the relation between recoder and KeY entities in a
     * bidirectional way.
     * <p>
     * It is used for syntactical structures and types.
     */
    private final KeYJPMapping mapping;

    /**
     * Counter used to enumerate the anonymous implicit classes used in parsing of Java Fragments
     */
    private static final AtomicInteger INTERACT_COUNTER = new AtomicInteger();

    /**
     * the object that handles the transformation from recoder AST to KeY AST
     */
    private final JP2KeYConverter converter;

    /**
     * the object that handles the transformation from recoder types to KeY
     * types
     */
    private final JP2KeYTypeConverter typeConverter;

    private final Services services;
    private final JavaParserFactory programFactory;

    /**
     * the File object that describes the directory from which the internal
     * classes are to be read. They are read in differently - therefore the
     * second category. A null value indicates that the boot classes are to
     * be read from an internal repository.
     */
    @NonNull
    private final Path bootClassPath;


    /**
     * A list of {@link File} objects that describes the classpath to be searched
     * for classes or Java files.
     */
    @NonNull
    private final Collection<Path> libraryPath;

    public JavaService(Services services, @NonNull Path bootClassPath,
            @NonNull Collection<Path> libraryPath) {
        this.services = services;
        this.mapping = new KeYJPMapping();
        this.bootClassPath = bootClassPath;
        this.libraryPath = libraryPath;
        programFactory = new JavaParserFactory(services);
        typeConverter = new JP2KeYTypeConverter(services, programFactory.getTypeSolver(), mapping);
        converter = new JP2KeYConverter(services, mapping, new Namespace<>(), typeConverter);
    }

    private JavaService(JavaService o, Services services) {
        this.services = services;
        this.bootClassPath = o.bootClassPath;
        this.libraryPath = o.libraryPath;
        this.mapping = o.mapping.copy();
        programFactory = o.programFactory.copy(services);
        typeConverter = new JP2KeYTypeConverter(services, programFactory.getTypeSolver(), mapping);
        converter = new JP2KeYConverter(services, mapping, new Namespace<>(), typeConverter);
    }

    public JavaService copy(Services services) {
        return new JavaService(this, services);
    }

    /**
     * return the associated converter object
     *
     * @return not null
     */
    public JP2KeYConverter getConverter(Namespace<SchemaVariable> schemaVariables) {
        return new JP2KeYConverter(services, mapping, schemaVariables, typeConverter);
    }

    /**
     * return the associated type converter object
     *
     * @return not null
     */
    @NonNull
    public JP2KeYTypeConverter getTypeConverter() {
        return typeConverter;
    }

    @NonNull
    public KeYJPMapping getMapping() {
        return mapping;
    }

    @NonNull
    public Path getBootClassPath() {
        return bootClassPath;
    }

    @NonNull
    public Collection<Path> getLibraryPath() {
        return Collections.unmodifiableCollection(libraryPath);
    }

    private static BuildingIssue buildingIssueFromProblem(String source, Problem problem) {
        var loc = problem.getLocation()
                .flatMap(TokenRange::toRange)
                .map(b -> b.begin)
                .orElse(new Position(-1, -1));
        return new BuildingIssue(problem.getVerboseMessage(),
            problem.getCause().orElse(null), false,
            de.uka.ilkd.key.java.Position.fromJPPosition(loc), source);
    }

    // region parsing of compilation units
    private <T> T unwrapParseResult(String source, ParseResult<T> result) {
        if (result.isSuccessful()) {
            assert result.getResult().isPresent();
            return result.getResult().get();
        }
        if (result.getProblems().isEmpty()) {
            throw new UnsupportedOperationException("Parser returned null value and no errors");
        }

        var errors = new ArrayList<BuildingIssue>(result.getProblems().size());
        for (Problem problem : result.getProblems()) { errors.add(buildingIssueFromProblem(source, problem)); }

        throw new BuildingExceptions(errors);
    }

    private ParseResult<CompilationUnit> parseCompilationUnit(Path filename,
            @Nullable FileRepo fileRepo) throws IOException {
        Reader is;
        if (fileRepo != null) {
            is = new InputStreamReader(fileRepo.getInputStream(filename));
        } else {
            is = Files.newBufferedReader(filename);
        }
        try (BufferedReader br = new BufferedReader(is)) {
            ParseResult<CompilationUnit> cu = programFactory.parseCompilationUnit(br);
            if (cu.getResult().isPresent()) { cu.getResult().get().setStorage(filename); }
            return cu;
        }
    }

    /**
     * read a compilation unit, given as a string.
     *
     * @param files
     *        where to read from
     * @param repo
     *        the repo to use for reading
     * @return a KeY structured compilation unit.
     */
    public <E extends Throwable> List<de.uka.ilkd.key.java.ast.CompilationUnit> readCompilationUnits(
            Path parent,
            Collection<Path> files, FileRepo repo,
            BiFunction<BuildingExceptions, Path, E> exceptionProvider)
            throws IOException, E {
        parseSpecialClasses();
        var cus = new ArrayList<CompilationUnit>(files.size());
        for (Path file : files) {
            try {
                var cu = unwrapParseResult(file.toString(), parseCompilationUnit(file, repo));
                if (cu.getPackageDeclaration().isEmpty()) {
                    fixupPackageDeclaration(cu, parent.relativize(file).toString());
                }
                cus.add(cu);
            } catch (BuildingExceptions e) {
                throw exceptionProvider.apply(e, file);
            }
        }
        programFactory.addUserClasses(cus);
        transformModel(Collections.unmodifiableList(cus));
        var result = new ArrayList<de.uka.ilkd.key.java.ast.CompilationUnit>(cus.size());
        for (CompilationUnit cu : cus) { result.add(converter.processCompilationUnit(cu)); }
        return result;
    }

    /**
     * read a compilation unit, given as a string.
     *
     * @param text
     *        a string represents a compilation unit
     * @return a KeY structured compilation unit.
     */
    public de.uka.ilkd.key.java.ast.CompilationUnit readCompilationUnit(String text) {
        parseSpecialClasses();
        LOGGER.debug("Reading {}", trim(text));
        var reader = new StringReader(text);
        var cu = unwrapParseResult("<string>", programFactory.parseCompilationUnit(reader));
        programFactory.addUserClasses(Collections.singletonList(cu));
        // transform program
        transformModel(Collections.singletonList(cu));
        return converter.processCompilationUnit(cu);
    }

    // ----- parsing libraries

    private static void fixupPackageDeclaration(CompilationUnit cu, String relativePath) {
        if (cu.getPackageDeclaration().isPresent()) { return; }
        if (relativePath == null) { throw new NullPointerException(); }
        var pkg = relativePath;
        if (pkg.endsWith(".java")) { pkg = pkg.substring(0, pkg.length() - 5); }
        pkg = pkg.replace('\\', '.').replace('/', '.');
        var lastDot = pkg.lastIndexOf('.');
        if (lastDot == -1) { return; }
        pkg = pkg.substring(0, lastDot);
        try {
            cu.setPackageDeclaration(pkg);
        } catch (ParseProblemException ignored) {
            LOGGER.warn("Failed to construct a package name for the java file " + relativePath
                    + ", it might contain invalid characters. "
                    + "Add a package declaration to the file or rename its folder");
        }
    }

    /**
     * This method loads the internal classes - also called the "boot" classes.
     * <p>
     * If the bootClassPath is set to null, it locates java classes that
     * are stored internally within the jar-file or the binary directory. The
     * JAVALANG.TXT file lists all files to be loaded.
     * <p>
     * If, however, the bootClassPath is assigned a value, this is treated
     * as a directory (not a JAR file at the moment) and all files in this
     * directory are read in. This is done using a
     * {@link DirectoryFileCollection}.
     *
     * @param fileRepo
     *        the FileRepo that provides the InputStream to resources
     * @return the compilation units
     */
    private List<CompilationUnit> parseBootClasses(FileRepo fileRepo) throws IOException {
        List<Path> paths;
        try (var stream = Files.walk(bootClassPath)) {
            paths = stream.filter(it -> {
                var name = it.getFileName().toString();
                return name.endsWith(".java") || name.endsWith(".jml");
            }).collect(Collectors.toList());
        }

        List<Pair<Path, ParseResult<CompilationUnit>>> compilationUnits = paths.stream()
                .filter(Objects::nonNull)
                .map(path -> {
                    try {
                        return new Pair<>(path, parseCompilationUnit(path, fileRepo));
                    } catch (IOException e) {
                        throw new RuntimeException(e);
                    }
                }).toList();

        if (compilationUnits.stream().allMatch(it -> it.second.isSuccessful())) {
            return compilationUnits.stream()
                    .map(it -> {
                        var cu = it.second.getResult().get();
                        fixupPackageDeclaration(cu, bootClassPath.relativize(it.first).toString());
                        return cu;
                    })
                    .collect(Collectors.toList());
        }

        var errors = compilationUnits.stream()
                .filter(c -> c.second.isSuccessful())
                .flatMap(c -> c.second.getProblems().stream()
                        .map(problem -> buildingIssueFromProblem(c.first.toString(), problem)))
                .collect(Collectors.toList());
        throw new BuildingExceptions(errors);
    }

    /**
     * reads compilation units that will be treated as library classes.
     * <p>
     * Proceed as follows:
     *
     * <ol>
     * <li>If "classPath" is set and contains at least one entry
     * <ol>
     * <li>read every <code>.java</code> file within the entries (directories
     * or zip files)
     * <li>read every <code>.class</code> file within the entries
     * (directories or zip files)
     * </ol>
     * <li>else read a special collection of classes that is stored internally
     * </ol>
     *
     * @param fileRepo
     *        the FileRepo for obtaining InputStreams
     * @throws IOException
     *         an exception
     * @author mulbrich
     */
    private List<CompilationUnit> parseLibraryClasses(FileRepo fileRepo) throws IOException {
        List<FileCollection> sources = new ArrayList<>();
        for (var cp : libraryPath) {
            if (Files.isDirectory(cp)) {
                sources.add(new DirectoryFileCollection(cp));
            } else {
                sources.add(new ZipFileCollection(cp));
            }
        }

        List<CompilationUnit> rcuList = new ArrayList<>();

        // -- read files --
        for (FileCollection fc : sources) {
            FileCollection.Walker walker = fc.createWalker(new String[] { ".jml", ".java" });
            while (walker.step()) {
                var currentDataLocation = walker.getCurrentLocation();
                var name = walker.getCurrentLocation().toString();
                try (InputStream is = walker.openCurrent(fileRepo);
                        Reader isr = new InputStreamReader(is);
                        Reader f = new BufferedReader(isr)) {
                    var cu = unwrapParseResult(name, programFactory.parseCompilationUnit(f));
                    fixupPackageDeclaration(cu, walker.getRelativeLocation());
                    cu.setStorage(currentDataLocation);
                    removeCodeFromClasses(cu, false);
                    rcuList.add(cu);
                }
            }
        }

        // -- read class files --
        // TODO javaparser
        /*
         * ClassFileDeclarationManager manager = new ClassFileDeclarationManager(pf);
         * ByteCodeParser parser = new ByteCodeParser();
         * for (FileCollection fc : sources) {
         * FileCollection.Walker walker = fc.createWalker(".class");
         * while (walker.step()) {
         * currentDataLocation = walker.getCurrentDataLocation();
         * try (InputStream is = new BufferedInputStream(walker.openCurrent(fileRepo))) {
         * ClassFile cf = parser.parseClassFile(is);
         * manager.addClassFile(cf, currentDataLocation);
         * } catch (Exception ex) {
         * throw new ConvertException("Error while loading: " + walker.getCurrentDataLocation(),
         * ex);
         * }
         * }
         * }
         * rcuList.addAll(manager.getCompilationUnits());
         */
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
                if (!allowed && n.getBody().isPresent()) {
                    LOGGER.warn("Method body of method {} should not be allowed: {}",
                        n.getNameAsString(),
                        rcu.getStorage().get().getPath());
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
        parseSpecialClasses(null);
    }

    /**
     * makes sure that the special classes (library classes) have been parsed
     * in.
     * <p>
     * If not parsed yet, the special classes are read in and converted.
     * This method throws only runtime exceptions for historical reasons.
     *
     * @param fileRepo
     *        the fileRepo which will store the files
     */
    public void parseSpecialClasses(FileRepo fileRepo) {
        if (mapping.setParsedSpecial())
            return;
        mapping.setParsedSpecial(true);
        try {
            parseBootClasspath(fileRepo);
            parseLibraryPaths(fileRepo);

            // Make sure some required types are registered
            for (var type : ResolvedPrimitiveType.values()) { typeConverter.getKeYJavaType(type); }
            typeConverter.getKeYJavaType(NullType.INSTANCE);
            typeConverter.getKeYJavaType(ResolvedVoidType.INSTANCE);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    private void parseLibraryPaths(FileRepo fileRepo) throws IOException {
        LOGGER.debug("Parsing library classes");
        var libraryClasses = parseLibraryClasses(fileRepo);
        programFactory.setLibraryClasses(libraryClasses);
        LOGGER.debug("Finished parsing library classes");

        transformModel(libraryClasses);

        /*
         * dynamicallyCreatedCompilationUnits = keySourceInfo.getCreatedStubClasses();
         * specialClasses.addAll(dynamicallyCreatedCompilationUnits);
         */

        for (CompilationUnit cu : libraryClasses) { converter.processCompilationUnit(cu); }
        LOGGER.debug("Finished processing library classes");
    }

    private void parseBootClasspath(FileRepo fileRepo) throws IOException {
        LOGGER.debug("Parsing internal classes from {}", bootClassPath);
        var bootClasses = parseBootClasses(fileRepo);

        /*
         * var defaultCu = unwrapParseResult(programFactory.parseCompilationUnit(
         * new StringReader("public class " + JavaInfo.DEFAULT_EXECUTION_CONTEXT_CLASS +
         * " { public static void " + JavaInfo.DEFAULT_EXECUTION_CONTEXT_METHOD
         * + "() {}  }")));
         * bootClasses.add(defaultCu);
         */

        programFactory.setBootClasses(bootClasses);
        LOGGER.debug("Finished parsing internal classes");

        transformModel(bootClasses);
        // Process java.lang.Object first (needed to construct array classes like int[]
        var object = bootClasses.stream()
                .filter(b -> b.getPrimaryType()
                        .map(t -> t.getFullyQualifiedName().orElseThrow()
                                .equals(TypeSolver.JAVA_LANG_OBJECT))
                        .orElse(false))
                .findFirst()
                .orElse(null);
        if (object != null) { converter.processCompilationUnit(object); }

        var obj = typeConverter.getObjectType();
        assert obj != null && obj.getJavaType() != null : "java.lang.Object has to be available";

        for (CompilationUnit cu : bootClasses) { if (cu == object) { continue; } converter.processCompilationUnit(cu); }
        LOGGER.debug("Finished processing internal classes");
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
     * @param cUnits
     *        a list of compilation units, not null.
     */
    protected void transformModel(List<CompilationUnit> cUnits) {
        // weigl: Exclude java fragments for speed-up:
        // These fragments are boring: No JML, no constructors, no initializer. And therefore
        // no need for pre-transformation.
        cUnits = cUnits.stream().filter(
            it -> !it.getType(0).getNameAsString().equals(JavaInfo.DEFAULT_EXECUTION_CONTEXT_CLASS))
                .collect(Collectors.toList());
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
     * @param block
     *        the StatementBlock to wrap
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
     * @param mdecl
     *        the declaration.MethodDeclaration to wrap
     * @param context
     *        the declaration.ClassDeclaration where the method
     *        has to be embedded
     * @return the enclosing declaration.ClassDeclaration
     */
    protected ClassOrInterfaceDeclaration embedMethod(MethodDeclaration mdecl,
            TypeScope.JPContext context) {
        ClassOrInterfaceDeclaration classContext = context.getClassDeclaration();
        classContext.addMember(mdecl);
        /*
         * for (int i = 0, sz = memberList.size(); i < sz; i++) {
         * if (memberList.get(i) instanceof MethodDeclaration) {
         * MethodDeclaration olddecl =
         * (MethodDeclaration) memberList.get(i);
         * if (olddecl.getName().equals(mdecl.getName())) {
         * memberList.remove(i);
         * }
         * }
         * }
         */
        return classContext;
    }

    /**
     * creates an empty RECODER compilation unit with a temporary name.
     *
     * @return the new CompilationUnit
     */
    public TypeScope.JPContext createEmptyContext() {
        var classContext = interactClassDecl();
        var cu = new CompilationUnit(null, new NodeList<>(), new NodeList<>(classContext), null);
        getSymbolResolver().inject(cu);
        return new TypeScope.JPContext(cu, classContext);
    }

    /**
     * create a new Context with a temporary name and make a list of variables
     * visible from within.
     *
     * @param vars
     *        a list of variables
     * @return a newly created context.
     */
    protected TypeScope.JPContext createContext(Iterable<ProgramVariable> vars) {
        var classContext = interactClassDecl();
        addProgramVariablesToClassContext(classContext, vars);
        var cu = new CompilationUnit(null, new NodeList<>(), new NodeList<>(classContext), null);
        getSymbolResolver().inject(cu);
        return new TypeScope.JPContext(cu, classContext);
    }

    /**
     * add a list of variables to a context
     *
     * @param classContext
     *        context to add to
     * @param vars
     *        vars to add
     */
    private void addProgramVariablesToClassContext(ClassOrInterfaceDeclaration classContext,
            Iterable<ProgramVariable> vars) {
        Set<String> names = new HashSet<>();

        for (ProgramVariable var : vars) {
            if (names.contains(var.name().toString())) { continue; }
            names.add(var.name().toString());

            if (var.getKeYJavaType() == null) {
                /// The program variable "variant" introduced to prove loop termination has sort
                /// "any" and, hence, no type. Parsing modalities fails on branches on which the
                /// variable exists. Therefore, it seems better to silently ignore such program
                /// variables (not making them accessible) rather than to throw an exception.
                /// MU 01.2019
                // throw new IllegalArgumentException("Variable " + var + " has no type");
                continue;
            }

            Type javaType = var.getKeYJavaType().getJavaType();
            if (javaType == null) { continue; }

            var existingSpec = lookupVarSpec(var);
            FieldSpecification keySpec;
            VariableDeclarator spec;
            if (existingSpec != null) {
                keySpec = (FieldSpecification) existingSpec;
                spec = (VariableDeclarator) Objects.requireNonNull(mapping.nodeFromKeY(keySpec));
            } else {
                keySpec = new FieldSpecification(var);
                spec = new VariableDeclarator(name2typeReference(javaType.getFullName()),
                    var.name().toString());
                mapping.put(spec, keySpec);
            }

            var field = new FieldDeclaration(new NodeList<>(), spec);
            classContext.addMember(field);

            var keyField = new de.uka.ilkd.key.java.ast.declaration.FieldDeclaration(
                new Modifier[0],
                new TypeRef(var.getKeYJavaType()),
                new FieldSpecification[] { keySpec },
                false);

            mapping.put(field, keyField);
        }
    }

    /**
     * look up in the mapping the variable specification for a program variable.
     * <p>
     * used by addProgramVariablesToClassContext
     */
    @Nullable
    private VariableSpecification lookupVarSpec(ProgramVariable pv) {
        for (final Object o : mapping.elemsKeY()) {
            if ((o instanceof VariableSpecification)
                    && ((VariableSpecification) o).getProgramVariable() == pv) {
                return (VariableSpecification) o;
            }
        }
        return null;
    }

    /**
     * given a name as string, construct a recoder type reference from it.
     *
     * @param typeName
     *        non-null type name as string
     * @return a freshly created type reference to the given type.
     */
    private com.github.javaparser.ast.type.Type name2typeReference(String typeName) {
        try {
            var p = PrimitiveType.Primitive.valueOf(typeName.toUpperCase());
            return new PrimitiveType(p);
        } catch (IllegalArgumentException e) {
            return new ClassOrInterfaceType(null, typeName);
        }
    }

    /**
     * parses a given JavaBlock using the context to determine the right
     * references and returns a statement block of recoder.
     *
     * @param input
     *        a String describing a java block
     * @param context
     *        CompilationUnit in which the block has to be
     *        interpreted
     * @return the parsed and resolved recoder statement block
     */
    Node parseBlock(String input, TypeScope.JPContext context) {
        parseSpecialClasses();
        // TODO javaparser change grammar of the parser to allow blocks without context information
        // Context-block
        Node original;
        BlockStmt block;
        if (input.contains("..") || input.contains("...")) {
            // TODO weigl further eloborate the situation, how to work with contexts provided?
            var b = unwrapParseResult("memory:/", programFactory.parseContextBlock(input));
            original = b;
            block = new BlockStmt(b.getStatements());
        } else { // Simple Java-block
            block = unwrapParseResult("memory:/", programFactory.parseStatementBlock(input));
            original = block;
        }
        // TODO javaparser result unused
        embedMethod(embedBlock(block), context);
        // normalise constant string expressions
        new ConstantStringExpressionEvaluator(createPipelineServices())
                .apply(context.getClassDeclaration());
        if (block != original) {
            var csb = (KeyContextStatementBlock) original;
            csb.setStatements(block.getStatements());
        }
        return original;
    }

    private TransformationPipelineServices createPipelineServices() {
        return createPipelineServices(new ArrayList<>(0));
    }

    private TransformationPipelineServices createPipelineServices(List<CompilationUnit> cUnits) {
        TransformationPipelineServices.TransformerCache cache =
            new TransformationPipelineServices.TransformerCache(cUnits);
        return new TransformationPipelineServices(programFactory, cache);
    }


    /**
     * parses a given JavaBlock using the context to determine the right
     * references
     *
     * @param block
     *        a String describing a java block
     * @param context
     *        CompilationUnit in which the block has to be
     *        interprested
     * @param allowSchemaJava
     *        if parameter is non-null SchemaJava is allowed and the namespace is
     *        used to resolve symbols
     * @return the parsed and resolved JavaBlock
     */
    public JavaBlock readBlock(String block, TypeScope.JPContext context,
            Namespace<SchemaVariable> allowSchemaJava) {
        var sb = parseBlock(block, context);
        if (allowSchemaJava == null && containsSchemaJava(sb)) {
            throw new RuntimeException("SchemaJava unexpected in the given block");
        }
        return JavaBlock
                .createJavaBlock((StatementBlock) getConverter(allowSchemaJava).process(sb));
    }

    private boolean containsSchemaJava(Node node) {
        return node.stream().anyMatch(it -> isSchemaJavaNode(node));
    }

    /**
     * A SchemaJava node is a node that represents a schema variable,e.g., {@code #s}.
     * We exploit the naming convention inside key-javaparser.
     *
     * @param node
     *        the node
     * @return true if type name of the node matches "Key*SV".
     */
    private boolean isSchemaJavaNode(@NonNull Node node) {
        String typeName = node.getMetaModel().getTypeName();
        return typeName.startsWith("Key") && typeName.endsWith("SV");
    }

    /**
     * parses a given JavaBlock using the context to determine the right
     * references using an empty context
     *
     * @param block
     *        a String describing a java block
     * @param allowSchemaJava
     *        if parameter is non-null SchemaJava is allowed and the namespace is
     *        used to resolve symbols
     * @return the parsed and resolved JavaBlock
     */
    public JavaBlock readBlockWithEmptyContext(String block,
            @Nullable Namespace<SchemaVariable> allowSchemaJava) {
        return readBlock(block, createEmptyContext(), allowSchemaJava);
    }

    /**
     * parses a given JavaBlock using a namespace to determine the right
     * references using an empty context. The variables of the namespace are
     * used to create a new class context
     *
     * @param allowSchemaJava
     *        if parameter is non-null SchemaJava is allowed and the namespace is
     *        used to resolve symbols
     * @param s
     *        a String describing a java block
     * @return the parsed and resolved JavaBlock
     */
    public JavaBlock readBlockWithProgramVariables(Namespace<IProgramVariable> variables, String s,
            Namespace<SchemaVariable> allowSchemaJava) {
        ImmutableList<ProgramVariable> pvs = ImmutableSLList.nil();
        for (IProgramVariable n : variables.allElements()) {
            if (n instanceof ProgramVariable) {
                pvs = pvs.append((ProgramVariable) n); // preserve the order (nested namespaces!)
            }
        }
        return readBlock(s, createContext(pvs), allowSchemaJava);
    }

    /**
     * make a new classdeclaration with a temporary name.
     * <p>
     * The name is a unique implicit identifier.
     *
     * @return a newly created recoder ClassDeclaration with a unique name
     */
    private ClassOrInterfaceDeclaration interactClassDecl() {
        return new CompilationUnit("$virtual_package_for_parsing")
                .addClass("$virtual_class_for_parsing" + INTERACT_COUNTER.incrementAndGet());
    }

    // ----- helpers

    /**
     * reduce the size of a string to a maximum of 150 characters. Introduces
     * ellipses [...]
     */
    private static String trim(String s) {
        if (s.length() > 150)
            return s.substring(0, 150 - 5) + "[...]";
        return s;
    }

    // ----- error handling

    public JavaParserFactory getProgramFactory() {
        return programFactory;
    }

    @NonNull
    private JavaSymbolSolver getSymbolResolver() {
        return programFactory.getSymbolSolver();
    }

    /*
     * public record LibraryFileParsingIssue(Path path, List<BuildingIssue> issues) {
     * }
     *
     * public static final class LibraryParsingException extends RuntimeException {
     * private final List<LibraryFileParsingIssue> issues;
     *
     * public LibraryParsingException(List<LibraryFileParsingIssue> issues) {
     * super("Parsing library classes failed");
     * this.issues = issues;
     * }
     *
     * public List<LibraryFileParsingIssue> getIssues() {
     * return issues;
     * }
     * }
     */
}
