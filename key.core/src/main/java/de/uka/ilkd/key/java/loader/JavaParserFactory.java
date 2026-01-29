/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.loader;

import java.io.Reader;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.ResolvedLogicalType;

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
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.google.common.cache.Cache;
import com.google.common.cache.CacheBuilder;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * @author Alexander Weigl
 * @version 1 (05.03.22)
 */
@NullMarked
public class JavaParserFactory {
    private @Nullable ParserConfiguration config;

    private final Services services;
    private final DynamicTypeSolver typeSolver = new DynamicTypeSolver();
    private final JavaSymbolSolver symbolResolver = new JavaSymbolSolver(typeSolver);
    private final List<CompilationUnit> bootClasses;
    private final List<CompilationUnit> libraryClasses;
    private final List<CompilationUnit> userClasses;


    public JavaParserFactory(Services services) {
        this.services = services;
        bootClasses = new ArrayList<>();
        libraryClasses = new ArrayList<>();
        userClasses = new ArrayList<>();
        typeSolver.lazyRebuild();
    }

    private JavaParserFactory(JavaParserFactory o, Services services) {
        this.services = services;
        // This is not a deep copy!
        // However, deep copying is pretty much impossible.
        // The KeyJPMapping has a reference to the old classes.
        // Therefore, doing a deep copy here "invalidates" all
        // existing KeyJavaTypes.
        bootClasses = new ArrayList<>(o.bootClasses);
        libraryClasses = new ArrayList<>(o.libraryClasses);
        userClasses = new ArrayList<>(o.userClasses);
        typeSolver.lazyRebuild();
    }

    public JavaParserFactory copy(Services services) {
        return new JavaParserFactory(this, services);
    }

    public void setBootClasses(Collection<CompilationUnit> classes) {
        bootClasses.clear();
        bootClasses.addAll(classes);
        typeSolver.lazyRebuild();
    }

    public void setLibraryClasses(Collection<CompilationUnit> classes) {
        libraryClasses.clear();
        libraryClasses.addAll(classes);
        typeSolver.lazyRebuild();
    }

    public void addUserClasses(Collection<CompilationUnit> classes) {
        userClasses.addAll(classes);
        typeSolver.lazyRebuild();
    }

    @NonNull
    private ParserConfiguration getConfiguration() {
        if (config == null) {
            config = new ParserConfiguration();
            config.setStoreTokens(true);
        }
        config.setSymbolResolver(getSymbolSolver());
        return config;
    }

    public JavaParser createJavaParser() {
        return new JavaParser(getConfiguration());
    }

    public TypeSolver getTypeSolver() {
        return typeSolver;
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

    public ParseResult<KeyContextStatementBlock> parseContextBlock(String sr) {
        return createJavaParser().parseSchemaBlock(sr);
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
            ct.add(new LogicalTypeSolver());
            ct.add(new ListTypeSolver(bootClasses));
            ct.add(new ListTypeSolver(libraryClasses));
            ct.add(new ListTypeSolver(userClasses));
            delegate = ct;
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

    private static class ListTypeSolver implements TypeSolver {
        private TypeSolver parent;
        private final Collection<CompilationUnit> units;

        private final Cache<String, SymbolReference<ResolvedReferenceTypeDeclaration>> foundTypes =
            CacheBuilder.newBuilder().softValues()
                    .maximumSize(1024)
                    .build();

        public ListTypeSolver(Collection<CompilationUnit> units) {
            this.units = units;
        }

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
            for (CompilationUnit unit : units) {
                final var primaryType = unit.getPrimaryType();
                if (primaryType.isPresent()) {
                    var cname = primaryType.get().getFullyQualifiedName();
                    if (cname.isPresent() && cname.get().equals(name)) {
                        return SymbolReference
                                .solved(JavaParserFacade.get(this)
                                        .getTypeDeclaration(primaryType.get()));
                    }
                }

                var packageName =
                    unit.getPackageDeclaration().map(p -> p.getName().asString()).orElse("");
                if (!name.startsWith(packageName)) {
                    continue;
                }
                // If we are looking in a compilation unit w/o a package name, we need to take the
                // whole name
                int packageNameStart = packageName.isEmpty() ? 0 : packageName.length() + 1;
                String localName =
                    name.substring(Math.min(name.length(), packageNameStart));
                var astTypeDeclaration = Navigator.findType(unit, localName);
                if (astTypeDeclaration.isPresent()) {
                    return SymbolReference
                            .solved(JavaParserFacade.get(this)
                                    .getTypeDeclaration(astTypeDeclaration.get()));
                }
            }
            return SymbolReference.unsolved();
        }
    }

    private class LogicalTypeSolver implements TypeSolver {

        private TypeSolver parent;

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
            if (name.contains("\\")) { // e.g., java.math.\bigint.
                name = "\\" + name.replaceFirst(".*\\\\", "");
                var kjt = services.getJavaInfo().getPrimitiveKeYJavaType(name);
                if (kjt != null) {
                    return SymbolReference.solved(new ResolvedLogicalType(kjt));
                }
            }
            return SymbolReference.unsolved();
        }
    }
}
