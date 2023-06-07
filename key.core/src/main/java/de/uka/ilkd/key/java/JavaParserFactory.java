package de.uka.ilkd.key.java;

import java.io.File;
import java.io.IOException;
import java.io.Reader;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.*;
import javax.annotation.Nonnull;
import javax.annotation.Nullable;

import org.key_project.util.java.IOUtil;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.key.sv.KeyContextStatementBlock;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.resolution.Navigator;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.resolution.declarations.ResolvedReferenceTypeDeclaration;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.javaparsermodel.JavaParserFacade;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ClassLoaderTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JarTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import com.google.common.cache.Cache;
import com.google.common.cache.CacheBuilder;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * @author Alexander Weigl
 * @version 1 (05.03.22)
 */
public class JavaParserFactory {
    private static final Logger LOGGER = LoggerFactory.getLogger(JavaParserFactory.class);

    /**
     * the File object that describes the directory from which the internal
     * classes are to be read. They are read in differently - therefore the
     * second category. A null value indicates that the boot classes are to
     * be read from an internal repository.
     */
    private Path bootClassPath;


    /**
     * A list of {@link File} objects that describes the classpath to be searched
     * for classes or Java files.
     */
    @Nonnull
    private final ArrayList<Path> sourcePaths;

    @Nullable
    private ParserConfiguration config;

    private final DynamicTypeSolver typeSolver = new DynamicTypeSolver();

    @Nonnull
    private final JavaSymbolSolver symbolResolver = new JavaSymbolSolver(typeSolver);


    @Nonnull
    private List<CompilationUnit> javaBootClassCollection = new ArrayList<>();

    private boolean useSystemClassLoaderInResolution;


    public JavaParserFactory(Path bootClassPath, Collection<Path> sourcePaths) {
        this.bootClassPath = bootClassPath;
        if (bootClassPath == null) {
            useSystemClassLoaderInResolution = true;// needed for finding java.lang.Object & Co.
        }
        this.sourcePaths = new ArrayList<>(sourcePaths);
        typeSolver.lazyRebuild();
    }

    @Nonnull
    public List<Path> getSourcePaths() {
        return Collections.unmodifiableList(sourcePaths);
    }

    public void setJavaRedux(Collection<CompilationUnit> redux) {
        javaBootClassCollection.clear();
        javaBootClassCollection.addAll(redux);
        typeSolver.lazyRebuild();
    }

    public void addSourcePaths(Collection<Path> files) {
        sourcePaths.ensureCapacity(sourcePaths.size() + files.size());
        for (Path path : files) {
            if (sourcePaths.contains(path)) {
                continue; // ignore that path is already set
            }
            for (Path existing : sourcePaths) {
                if (path.startsWith(existing)) {
                    throw new IllegalStateException(
                        "A parent of this path is already given in the classpath");
                }

                if (existing.startsWith(path)) {
                    throw new IllegalStateException(
                        "A child folder of this path is already given in the classpath");
                }
            }
            sourcePaths.add(path);
        }

        typeSolver.lazyRebuild();
    }

    @Nonnull
    private ParserConfiguration getConfiguration() {
        if (config == null) {
            config = new ParserConfiguration();
            config.setStoreTokens(true);
        }
        config.setSymbolResolver(getSymbolResolver());
        return config;
    }

    @Nonnull
    private JavaSymbolSolver getSymbolResolver() {
        return symbolResolver;
    }

    @Nonnull
    public JavaParser createJavaParser() {
        return new JavaParser(getConfiguration());
    }

    @Nonnull
    public TypeSolver getTypeSolver() {
        return typeSolver;
    }

    /**
     * If set to true the symbol solver do not use the {@link ClassLoaderTypeSolver} with the system
     * class class loader.
     * This means, that classes defined by the JRE are not found, if they are not given in the class
     * path.
     * In particular, only JavaRedux and Red classes (if added) are
     * the next parser runs
     */
    public void setUseSystemClassLoaderInResolution(boolean useSystemClassLoaderInResolution) {
        this.useSystemClassLoaderInResolution = useSystemClassLoaderInResolution;
        typeSolver.lazyRebuild();
    }

    @Nonnull
    public JavaSymbolSolver getSymbolSolver() {
        return symbolResolver;
    }

    public ParseResult<CompilationUnit> parseCompilationUnit(Reader reader) {
        return createJavaParser().parse(reader);
    }

    public ParseResult<BlockStmt> parseStatementBlock(String sr) {
        return createJavaParser().parseBlock(sr);
    }

    public ParseResult<KeyContextStatementBlock> parseContextBlock(String sr) {
        return createJavaParser().parseSchemaBlock(sr);
    }

    public void setBootClassPath(Path bootClassPath) {
        this.bootClassPath = bootClassPath;
        this.typeSolver.rebuild();
    }

    public Path getBootClassPath() {
        return bootClassPath;
    }

    /**
     * A wrapper do make the type solver dynamic and aware of sourcePath changes.
     * The type solver is an attribute of {@link CompilationUnit} which are used to resolve types.
     * But it is rather a fixed value, that is set by the preprocessing in {@link JavaParser}. To
     * make the type solving
     * aware of changes to this instance without changing the behavior of JP, we introduce one
     * indirection with this class.
     * This class behaves like a {@link TypeSolver} because everything is delegated to an intenral
     * {@link CombinedTypeSolver},
     * which is rebuild on changes on the outer instance.
     * <p>
     * Use {@link #rebuild()} to trigger a rebuild of the type solver on changing relevant setting
     * in the outer
     * instance.
     *
     * @author Alexander Weigl
     */
    private class DynamicTypeSolver implements TypeSolver {
        private TypeSolver delegate;
        private TypeSolver parent;

        /**
         * rebuilds the type solver.
         */
        void rebuild() {
            var ct = new CombinedTypeSolver();
            if (javaBootClassCollection.isEmpty()) {
                addToTypeSolver(ct, bootClassPath);
            } else {
                var ts = new ListTypeSolver();
                ct.add(ts);
            }


            for (var sourcePath : sourcePaths) {
                addToTypeSolver(ct, sourcePath);
            }

            /*
             * if (useSystemClassLoaderInResolution) {
             * ct.add(new ReflectionTypeSolver(true));
             * }
             */
            delegate = ct;
        }


        private void addToTypeSolver(CombinedTypeSolver ct, Path sourcePath) {
            if (sourcePath == null)
                return;
            if (IOUtil.isFolderInsideJar(sourcePath)) {
                try {
                    var fsPath = IOUtil.openFileInJar(sourcePath);
                    ct.add(new JavaParserTypeSolver(fsPath, getConfiguration()));
                } catch (IOException e) {
                    throw new RuntimeException(e);
                }
                return;
            }

            if (Files.isRegularFile(sourcePath) && sourcePath.getFileName().endsWith(".jar")) {
                try {
                    ct.add(new JarTypeSolver(sourcePath));
                } catch (IOException e) {
                    LOGGER.error(e.getMessage(), e);
                }
                return;
            }

            if (Files.isDirectory(sourcePath)) {
                ct.add(new JavaParserTypeSolver(sourcePath, getConfiguration()));
                return;
            }

            LOGGER.error(
                "You gave me {} to add into the classpath. But I am not aware how to handle this path",
                sourcePath);
        }

        @Override
        public TypeSolver getParent() {
            return parent;
        }

        @Override
        public void setParent(TypeSolver parent) {
            this.parent = parent;
        }

        void lazyRebuild() {
            delegate = null;
        }

        @Override
        public SymbolReference<ResolvedReferenceTypeDeclaration> tryToSolveType(String name) {
            if (delegate == null)
                rebuild();
            return delegate.tryToSolveType(name);
        }
    }

    private class ListTypeSolver implements TypeSolver {
        private TypeSolver parent;

        private final Cache<String, SymbolReference<ResolvedReferenceTypeDeclaration>> foundTypes =
            CacheBuilder.newBuilder().softValues()
                    .maximumSize(1024)
                    .build();

        @Override
        public TypeSolver getParent() {
            return parent;
        }

        @Override
        public void setParent(TypeSolver parent) {
            this.parent = parent;
        }

        @Override
        public SymbolReference<ResolvedReferenceTypeDeclaration> tryToSolveType(String name) {
            SymbolReference<ResolvedReferenceTypeDeclaration> cachedValue =
                foundTypes.getIfPresent(name);
            if (cachedValue != null) {
                return cachedValue;
            }

            // Otherwise load it
            SymbolReference<ResolvedReferenceTypeDeclaration> result = tryToSolveTypeUncached(name);
            foundTypes.put(name, result);
            return result;
        }

        private SymbolReference<ResolvedReferenceTypeDeclaration> tryToSolveTypeUncached(
                String name) {
            for (CompilationUnit unit : javaBootClassCollection) {

                final var primaryType = unit.getPrimaryType();
                if (primaryType.isPresent()) {
                    var cname = primaryType.get().getFullyQualifiedName();
                    if (cname.isPresent() && cname.get().equals(name)) {
                        return SymbolReference
                                .solved(JavaParserFacade.get(this)
                                        .getTypeDeclaration(primaryType.get()));
                    }
                }

                var astTypeDeclaration = Navigator.findType(unit, name);
                if (astTypeDeclaration.isPresent()) {
                    return SymbolReference
                            .solved(JavaParserFacade.get(this)
                                    .getTypeDeclaration(astTypeDeclaration.get()));
                }
            }
            return SymbolReference.unsolved();
        }
    }
}
