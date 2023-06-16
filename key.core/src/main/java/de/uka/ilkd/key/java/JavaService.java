package de.uka.ilkd.key.java;

import java.io.*;
import java.net.URI;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Collectors;
import javax.annotation.Nonnull;
import javax.annotation.Nullable;

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
import de.uka.ilkd.key.util.DirectoryFileCollection;
import de.uka.ilkd.key.util.FileCollection;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.ZipFileCollection;
import de.uka.ilkd.key.util.parsing.BuildingExceptions;
import de.uka.ilkd.key.util.parsing.BuildingIssue;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import com.github.javaparser.ParseResult;
import com.github.javaparser.Position;
import com.github.javaparser.Problem;
import com.github.javaparser.TokenRange;
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
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
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
    public JP2KeYTypeConverter getTypeConverter() {
        return typeConverter;
    }

    private static BuildingIssue buildingIssueFromProblem(Problem problem) {
        LOGGER.error(problem.toString(), problem.getCause().orElse(null));
        var loc = problem.getLocation()
                .flatMap(TokenRange::toRange)
                .map(b -> b.begin)
                .orElse(new Position(-1, -1));
        return new BuildingIssue(problem.getVerboseMessage(),
            problem.getCause().orElse(null), false,
            de.uka.ilkd.key.java.Position.fromJPPosition(loc));
    }

    // region parsing of compilation units
    private <T> T unwrapParseResult(ParseResult<T> result) {
        if (result.isSuccessful()) {
            assert result.getResult().isPresent();
            return result.getResult().get();
        }
        if (result.getProblems().isEmpty()) {
            throw new UnsupportedOperationException("Parser returned null value and no errors");
        }

        var errors = new ArrayList<BuildingIssue>(result.getProblems().size());
        for (Problem problem : result.getProblems()) {
            if (problem.getMessage().contains("ghost")) {
                // TODO javaparser A hack to remove false alarm caused by ModifiersVisitor check
                continue;
            }

            errors.add(buildingIssueFromProblem(problem));
        }

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
            if (cu.getResult().isPresent()) {
                cu.getResult().get().setStorage(filename);
            }
            return cu;
        }
    }

    /**
     * read a compilation unit, given as a string.
     *
     * @param file where to read from
     * @param repo the repo to use for reading
     * @return a KeY structured compilation unit.
     */
    public de.uka.ilkd.key.java.CompilationUnit readCompilationUnit(Path file, FileRepo repo)
            throws IOException {
        parseSpecialClasses();
        // TODO javaparser problem: method used in foreach loop, pipeline should be used with all
        // files at once
        // However, unwrapParseResult does not contain any file related info
        var cu = unwrapParseResult(parseCompilationUnit(file, repo));
        transformModel(Collections.singletonList(cu));
        return converter.processCompilationUnit(cu);
    }

    /**
     * read a compilation unit, given as a string.
     *
     * @param text a string represents a compilation unit
     * @return a KeY structured compilation unit.
     */
    public de.uka.ilkd.key.java.CompilationUnit readCompilationUnit(String text) {
        parseSpecialClasses();
        LOGGER.debug("Reading {}", trim(text));
        var reader = new StringReader(text);
        var cu = unwrapParseResult(programFactory.parseCompilationUnit(reader));

        // TODO javaparser why? this method is used in tests only
        programFactory.appendToJavaRedux(Collections.singletonList(cu));
        // transform program
        transformModel(Collections.singletonList(cu));
        return converter.processCompilationUnit(cu);
    }

    // ----- parsing libraries

    public void setClassPath(Path bootClassPath, List<Path> classPath) {
        programFactory.setBootClassPath(bootClassPath);
        programFactory.addSourcePaths(classPath);
    }

    /**
     * This method loads the internal classes - also called the "boot" classes.
     * <p>
     * If the bootClassPath is set to null, it locates java classes that
     * are stored internally within the jar-file or the binary directory. The
     * JAVALANG.TXT file lists all files to be loaded. The files are found using
     * a special {@link JavaReduxFileCollection}.
     * <p>
     * If, however, the bootClassPath is assigned a value, this is treated
     * as a directory (not a JAR file at the moment) and all files in this
     * directory are read in. This is done using a
     * {@link DirectoryFileCollection}.
     *
     * @param fileRepo the FileRepo that provides the InputStream to resources
     * @return the compilation units
     */
    private List<CompilationUnit> parseInternalClasses(FileRepo fileRepo) throws IOException {
        List<URI> paths;

        if (programFactory.getBootClassPath() == null) {
            var bootCollection = new JavaReduxFileCollection(services.getProfile());
            paths = bootCollection.getResources().collect(Collectors.toList());
        } else {
            try (var stream = Files.walk(programFactory.getBootClassPath())) {
                paths = stream.filter(it -> {
                    var name = it.getFileName().toString();
                    return name.endsWith(".java") || name.endsWith(".jml");
                }).map(Path::toUri).collect(Collectors.toList());
            }
        }

        List<Pair<Path, ParseResult<CompilationUnit>>> compilationUnits = paths.stream()
                .filter(Objects::nonNull)
                .map(it -> {
                    try {
                        var path = Paths.get(it);
                        return new Pair<>(path, parseCompilationUnit(path, fileRepo));
                    } catch (IOException e) {
                        throw new RuntimeException(e);
                    }
                }).toList();

        if (compilationUnits.stream().allMatch(it -> it.second.isSuccessful())) {
            return compilationUnits.stream().map(it -> it.second.getResult().get()).toList();
        }

        var errors = compilationUnits.stream()
                .filter(c -> c.second.isSuccessful())
                .map(c -> new LibraryFileParsingIssue(
                    c.first,
                    c.second.getProblems().stream().map(JavaService::buildingIssueFromProblem)
                            .toList()))
                .toList();
        throw new LibraryParsingException(errors);
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
     * @param fileRepo the FileRepo for obtaining InputStreams
     * @throws IOException an exception
     * @author mulbrich
     */
    private List<CompilationUnit> parseLibs(FileRepo fileRepo) throws IOException {
        LOGGER.debug("Parsing libs");
        var internal = parseInternalClasses(fileRepo);
        List<FileCollection> sources = new ArrayList<>();
        List<CompilationUnit> rcuList = new ArrayList<>(internal);

        for (var cp : programFactory.getSourcePaths()) {
            if (Files.isDirectory(cp)) {
                sources.add(new DirectoryFileCollection(cp.toFile()));
            } else {
                sources.add(new ZipFileCollection(cp.toFile()));
            }
        }

        /*
         * While the resources are read (and possibly copied) via the FileRepo, the data location
         * is left as it is. This leaves the line information intact.
         */

        // -- read jml files --
        for (FileCollection fc : sources) {
            FileCollection.Walker walker = fc.createWalker(".jml");
            while (walker.step()) {
                var currentDataLocation = walker.getCurrentLocation();
                try (InputStream is = walker.openCurrent(fileRepo);
                        Reader isr = new InputStreamReader(is);
                        Reader f = new BufferedReader(isr)) {
                    var cu = unwrapParseResult(programFactory.parseCompilationUnit(f));
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
                var currentDataLocation = walker.getCurrentLocation();
                try (InputStream is = walker.openCurrent(fileRepo);
                        Reader isr = new InputStreamReader(is);
                        Reader f = new BufferedReader(isr)) {
                    var cu = unwrapParseResult(programFactory.parseCompilationUnit(f));
                    cu.setStorage(currentDataLocation);
                    removeCodeFromClasses(cu, true);
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

        var cu = unwrapParseResult(programFactory.parseCompilationUnit(
            new StringReader("public class " + JavaInfo.DEFAULT_EXECUTION_CONTEXT_CLASS +
                " { public static void " + JavaInfo.DEFAULT_EXECUTION_CONTEXT_METHOD
                + "() {}  }")));
        rcuList.add(cu);
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
                    LOGGER.warn("Method body ({}) should not be allowed: {}", n.getNameAsString(),
                        rcu.getStorage());
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
     * @param fileRepo the fileRepo which will store the files
     */
    public void parseSpecialClasses(FileRepo fileRepo) {
        if (mapping.parsedSpecial()) {
            return;
        }

        try {
            List<CompilationUnit> specialClasses = parseLibs(fileRepo);
            /*
             * dynamicallyCreatedCompilationUnits = keySourceInfo.getCreatedStubClasses();
             * specialClasses.addAll(dynamicallyCreatedCompilationUnits);
             * keySourceInfo.setIgnoreUnresolvedClasses(false);
             * changeHistory.updateModel();
             */
            programFactory.setJavaRedux(specialClasses);
            transformModel(specialClasses);

            // make them available to the rec2key mapping
            for (CompilationUnit cu : specialClasses) {
                // weigl: allowed for fragments
                // var dl = cu.getStorage();
                // if (dl.isEmpty())
                // throw new AssertionError("DataLocation not set on compilation unit");
                converter.processCompilationUnit(cu);
            }

            /*
             * TODO weigl
             * // Ensure that rec2key is complete (at least the NullType needs to be available!)
             * if (!rec2key().mapped(getNameInfo().getNullType())) {
             * Sort objectSort = services.getNamespaces().sorts().lookup(new
             * Name("java.lang.Object"));
             * assert objectSort != null;
             * NullSort nullSort = new NullSort(objectSort);
             * KeYJavaType result = new KeYJavaType(NullType.JAVA_NULL, nullSort);
             * if (services.getNamespaces().sorts().lookup(nullSort.name()) == null) {
             * services.getNamespaces().sorts().add(nullSort);
             * }
             * rec2key().put(servConf.getNameInfo().getNullType(), result);
             * }
             */

        } catch (IOException e) {
            throw new RuntimeException(e);
        }

        // tell the mapping that we have parsed the special classes
        mapping.parsedSpecial(true);
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
     * @param mdecl the declaration.MethodDeclaration to wrap
     * @param context the declaration.ClassDeclaration where the method
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
     * @param vars a list of variables
     * @return a newly created context.
     */
    protected TypeScope.JPContext createContext(ImmutableList<ProgramVariable> vars) {
        var classContext = interactClassDecl();
        addProgramVariablesToClassContext(classContext, vars);
        var cu = new CompilationUnit(null, new NodeList<>(), new NodeList<>(classContext), null);
        getSymbolResolver().inject(cu);
        return new TypeScope.JPContext(cu, classContext);
    }

    /**
     * add a list of variables to a context
     *
     * @param classContext context to add to
     * @param vars vars to add
     */
    private void addProgramVariablesToClassContext(ClassOrInterfaceDeclaration classContext,
            ImmutableList<ProgramVariable> vars) {
        Set<String> names = new HashSet<>();

        for (ProgramVariable var : vars) {
            if (names.contains(var.name().toString())) {
                continue;
            }
            names.add(var.name().toString());

            if (var.getKeYJavaType() == null) {
                /// The program variable "variant" introduced to prove loop termination has sort
                /// "any" and, hence, no type. Parsing modalities fails on branches on which the
                /// variable exists. Therefore, it seems better to silently ignore such program
                /// variables (not making themaccessible) rather than to throw an exception.
                /// MU 01.2019
                // throw new IllegalArgumentException("Variable " + var + " has no type");
                continue;
            }

            VariableSpecification keyVarSpec =
                lookupVarSpec(var).orElseGet(() -> new FieldSpecification(var));

            Type javaType = var.getKeYJavaType().getJavaType();
            if (javaType == null)
                continue;
            String typeName = javaType.getFullName();


            var decl = new VariableDeclarator(name2typeReference(typeName), keyVarSpec.getName());
            var field = new FieldDeclaration(new NodeList<>(), decl);

            classContext.addMember(field);
        }
    }

    /**
     * look up in the mapping the variable specification for a program variable.
     * <p>
     * used by addProgramVariablesToClassContext
     */
    private Optional<VariableSpecification> lookupVarSpec(ProgramVariable pv) {
        for (final Object o : mapping.elemsKeY()) {
            if ((o instanceof VariableSpecification)
                    && ((VariableSpecification) o).getProgramVariable() == pv) {
                return Optional.of((VariableSpecification) o);
            }
        }
        return Optional.empty();
    }

    /**
     * given a name as string, construct a recoder type reference from it.
     *
     * @param typeName non-null type name as string
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
     * @param input a String describing a java block
     * @param context CompilationUnit in which the block has to be
     *        interpreted
     * @return the parsed and resolved recoder statement block
     */
    BlockStmt parseBlock(String input, TypeScope.JPContext context) {
        parseSpecialClasses();
        // TODO javaparser change grammar of the parser to allow blocks without context information
        // Context-block
        BlockStmt block;
        if (input.contains("..") || input.contains("...")) {
            // TODO weigl further eloborate the situation, how to work with contexts provided?
            KeyContextStatementBlock blockStmt =
                unwrapParseResult(programFactory.parseContextBlock(input));
            block = new BlockStmt(blockStmt.getStatements());
        } else { // Simple Java-block
            block = unwrapParseResult(programFactory.parseStatementBlock(input));
        }
        // TODO javaparser result unused
        embedMethod(embedBlock(block), context);
        // normalise constant string expressions
        new ConstantStringExpressionEvaluator(createPipelineServices())
                .apply(context.getClassDeclaration());
        return block;
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
     * @param block a String describing a java block
     * @param context CompilationUnit in which the block has to be
     *        interprested
     * @param allowSchemaJava if parameter is non-null SchemaJava is allowed and the namespace is
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
     * @param node the node
     * @return true if type name of the node matches "Key*SV".
     */
    private boolean isSchemaJavaNode(@Nonnull Node node) {
        String typeName = node.getMetaModel().getTypeName();
        return typeName.startsWith("Key") && typeName.endsWith("SV");
    }

    /**
     * parses a given JavaBlock using the context to determine the right
     * references using an empty context
     *
     * @param block a String describing a java block
     * @param allowSchemaJava if parameter is non-null SchemaJava is allowed and the namespace is
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
     * @param allowSchemaJava if parameter is non-null SchemaJava is allowed and the namespace is
     *        used to resolve symbols
     * @param s a String describing a java block
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
    public JavaService(Services services, KeYJPMapping mapping, Path bootClassPath,
            Collection<Path> sourcePaths) {
        this.services = services;
        this.mapping = mapping;
        programFactory = new JavaParserFactory(bootClassPath, sourcePaths);
        typeConverter = new JP2KeYTypeConverter(services, programFactory.getTypeSolver(), mapping);
        converter = new JP2KeYConverter(services, mapping, new Namespace<>(), typeConverter);
    }


    public JavaParserFactory getProgramFactory() {
        return programFactory;
    }

    @Nonnull
    private JavaSymbolSolver getSymbolResolver() {
        return programFactory.getSymbolSolver();
    }

    public record LibraryFileParsingIssue(Path path, List<BuildingIssue> issues) {
    }

    public static final class LibraryParsingException extends RuntimeException {
        private final List<LibraryFileParsingIssue> issues;

        public LibraryParsingException(List<LibraryFileParsingIssue> issues) {
            super("Parsing library classes failed");
            this.issues = issues;
        }

        public List<LibraryFileParsingIssue> getIssues() {
            return issues;
        }
    }
}
