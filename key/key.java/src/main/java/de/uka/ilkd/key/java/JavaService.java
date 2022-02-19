package de.uka.ilkd.key.java;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.resolution.SymbolResolver;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.model.resolution.TypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ClassLoaderTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JarTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.JavaParserTypeSolver;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import recoder.util.Debug;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (19.02.22)
 */
public class JavaService {
    private static final Logger LOGGER = LoggerFactory.getLogger(JavaService.class);

    @Nonnull
    private final List<File> sourcePaths;
    @Nullable
    private ParserConfiguration config;
    @Nullable
    private TypeSolver typeSolver;

    @Nullable
    private SymbolResolver symbolResolver;

    public JavaService(Collection<File> sourcePaths) {
        this.sourcePaths = new ArrayList<>(sourcePaths);
    }

    public JavaParser createJavaParser() {
        return new JavaParser(getConfiguration());
    }

    @Nonnull
    private ParserConfiguration getConfiguration() {
        if (config == null) {
            config = new ParserConfiguration();
            config.setSymbolResolver(getSymbolResolver());
        }
        return config;
    }

    @Nonnull
    private SymbolResolver getSymbolResolver() {
        if (symbolResolver == null) {
            symbolResolver = new JavaSymbolSolver(getTypeSolver());
        }
        return symbolResolver;
    }


    public TypeSolver getTypeSolver() {
        if (typeSolver == null) {
            var ct = new CombinedTypeSolver();
            for (File sourcePath : sourcePaths) {
                if (sourcePath.isFile() && sourcePath.getName().endsWith(".jar")) {
                    try {
                        ct.add(new JarTypeSolver(sourcePath));
                    } catch (IOException e) {
                        LOGGER.error(e.getMessage(), e);
                    }
                } else if (sourcePath.isDirectory()) {
                    ct.add(new JavaParserTypeSolver(sourcePath, config));
                }
            }
            ct.add(new ClassLoaderTypeSolver(ClassLoader.getSystemClassLoader()));
            typeSolver = ct;
        }
        return typeSolver;
    }
}
