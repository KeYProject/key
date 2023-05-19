package de.uka.ilkd.key.java;

import java.io.File;
import java.io.IOException;
import java.io.Reader;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import javax.annotation.Nonnull;
import javax.annotation.Nullable;

import de.uka.ilkd.key.java.transformations.ConstantExpressionEvaluator;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.*;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * @author Alexander Weigl
 * @version 1 (05.03.22)
 */
public class JavaParserFactory {
    private static final Logger LOGGER = LoggerFactory.getLogger(JavaParserFactory.class);

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

    public JavaParserFactory(Collection<Path> sourcePaths) {
        this.sourcePaths = new ArrayList<>(sourcePaths);
    }

    @Nonnull
    public List<Path> getSourcePaths() {
        return Collections.unmodifiableList(sourcePaths);
    }

    public void setSourcePaths(List<Path> files) {
        this.sourcePaths.clear();
        this.sourcePaths.addAll(files);
        typeSolver = null;
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

    public JavaParser createJavaParser() {
        return new JavaParser(getConfiguration());
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
                        /*
                         * sourcePath.getRoot();
                         * final Matcher matcher = IOUtil.URL_JAR_FILE.matcher();
                         * if (matcher.matches()) {
                         */
                        // TODO javaparser add support for java files inside
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
     * If set to true the symbol solver do not use the {@link ClassLoaderTypeSolver} with the system
     * class class loader.
     * This means, that classes defined by the JRE are not found, if they are not given in the class
     * path.
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

    public JavaSymbolSolver getSymbolSolver() {
        return symbolResolver;
    }

    public ParseResult<CompilationUnit> parseCompilationUnit(Reader reader) {
        return createJavaParser().parse(reader);
    }

    public ParseResult<BlockStmt> parseStatementBlock(String sr) {
        return createJavaParser().parseBlock(sr);
    }

    public ConstantExpressionEvaluator createConstantExpressionEvaluator() {
        return new ConstantExpressionEvaluator(createJavaParser());
    }
}
