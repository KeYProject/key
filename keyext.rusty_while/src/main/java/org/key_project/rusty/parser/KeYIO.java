/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser;

import java.io.IOException;
import java.net.URL;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import org.key_project.logic.Namespace;
import org.key_project.logic.Term;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.NamespaceSet;
import org.key_project.rusty.logic.op.sv.SchemaVariable;
import org.key_project.rusty.parser.builder.*;
import org.key_project.rusty.proof.init.ProblemInitializer;
import org.key_project.rusty.rule.Taclet;
import org.key_project.rusty.util.parsing.BuildingException;
import org.key_project.rusty.util.parsing.BuildingIssue;

import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

import static org.key_project.rusty.parser.ParsingFacade.parseFiles;

public class KeYIO {
    private final Services services;
    private final NamespaceSet nss;
    private Namespace<@Nullable SchemaVariable> schemaNamespace;
    private List<BuildingIssue> warnings = new LinkedList<>();

    public KeYIO(@NonNull Services services, @NonNull NamespaceSet nss) {
        this.services = services;
        this.nss = nss;
    }

    public KeYIO(Services services) {
        this(services, services.getNamespaces());
    }

    /**
     * @param ctx
     * @return
     */
    public List<BuildingIssue> evalDeclarations(KeYAst.File ctx) {
        DeclarationBuilder declBuilder = new DeclarationBuilder(services, nss);
        ctx.accept(declBuilder);
        warnings.addAll(declBuilder.getBuildingIssues());
        return declBuilder.getBuildingIssues();
    }

    /**
     * @param ctx
     */
    public List<BuildingIssue> evalFuncAndPred(KeYAst.File ctx) {
        FunctionPredicateBuilder visitor = new FunctionPredicateBuilder(services, nss);
        ctx.accept(visitor);
        warnings.addAll(visitor.getBuildingIssues());
        return visitor.getBuildingIssues();
    }

    public List<BuildingIssue> getWarnings() {
        return warnings;
    }

    /**
     * Given an input string, this function returns a term if parsable.
     *
     * @param expr a valid stream
     * @return a valid term
     * @throws BuildingException if an unrecoverable error during construction or parsing happened
     */
    public @NonNull Term parseExpression(@NonNull String expr) {
        return parseExpression(CharStreams.fromString(expr));
    }

    /**
     * Given an input stream, this function returns an term if parsable.
     *
     * @param stream a valid stream
     * @return a valid term
     * @throws BuildingException if an unrecoverable error during construction or parsing happened
     */
    public @NonNull Term parseExpression(@NonNull CharStream stream) {
        KeYAst.Term ctx = ParsingFacade.parseExpression(stream);
        ExpressionBuilder visitor = new ExpressionBuilder(services, nss);
        /*
         * visitor.setAbbrevMap(abbrevMap);
         * if (schemaNamespace != null) {
         * visitor.setSchemaVariables(schemaNamespace);
         * }
         */
        Term t = (Term) ctx.accept(visitor);
        warnings = visitor.getBuildingIssues();
        return t;
    }

    public Loader load(CharStream content) {
        return new Loader(content, null);
    }

    /**
     * Loading of complete KeY files into the given schema. Supports recursive loading, but does not
     * provide support for Java and Java type informations.
     * <p>
     * Little sister of {@link ProblemInitializer}.
     *
     * TODO: Remove?
     */
    public class Loader {
        private final URL resource;
        private final CharStream content;
        private List<KeYAst.File> ctx = new LinkedList<>();
        private Namespace<@NonNull SchemaVariable> schemaNamespace;

        Loader(URL resource) {
            this(null, resource);
        }

        Loader(CharStream content, URL url) {
            resource = url;
            this.content = content;
        }

        public Namespace<SchemaVariable> getSchemaNamespace() {
            return schemaNamespace;
        }

        public List<Taclet> loadComplete() throws IOException {
            if (ctx.isEmpty()) {
                parseFile();
            }
            loadDeclarations();
            loadSndDegreeDeclarations();
            activateLDTs();
            return loadTaclets();
        }

        public Loader activateLDTs() {
            services.initLDTs();
            return this;
        }

        public Loader parseFile() throws IOException {
            if (!ctx.isEmpty()) {
                return this;
            }
            long start = System.currentTimeMillis();
            if (resource != null) {
                ctx = parseFiles(resource);
            } else {
                KeYAst.File c = ParsingFacade.parseFile(content);
                ctx.add(c);
            }
            long stop = System.currentTimeMillis();
            return this;
        }

        public ProblemInformation getProblemInformation() {
            if (ctx.isEmpty()) {
                throw new IllegalStateException("No files loaded.");
            }
            return ctx.get(0).getProblemInformation();
        }

        public Loader loadDeclarations() {
            DeclarationBuilder declBuilder = new DeclarationBuilder(services, nss);
            for (int i = ctx.size() - 1; i >= 0; --i) {
                var file = ctx.get(i);
                file.accept(declBuilder);
            }
            return this;
        }

        public Loader loadSndDegreeDeclarations() {
            FunctionPredicateBuilder visitor = new FunctionPredicateBuilder(services, nss);
            for (int i = ctx.size() - 1; i >= 0; --i) {
                KeYAst.File s = ctx.get(i);
                s.accept(visitor);
            }
            return this;
        }

        public ProblemFinder loadProblem() {
            if (ctx.isEmpty()) {
                throw new IllegalStateException();
            }
            ProblemFinder pf = new ProblemFinder(services, nss);
            ctx.get(0).accept(pf);
            return pf;
        }

        public List<Taclet> loadTaclets() {
            if (ctx.isEmpty()) {
                throw new IllegalStateException();
            }
            List<TacletPBuilder> parsers = ctx.stream().map(it -> new TacletPBuilder(services, nss))
                    .toList();
            List<Taclet> taclets = new ArrayList<>(2048);
            for (int i = 0; i < ctx.size(); i++) {
                KeYAst.File s = ctx.get(i);
                TacletPBuilder p = parsers.get(i);
                if (KeYIO.this.schemaNamespace != null) {
                    p.setSchemaVariables(new Namespace<>(KeYIO.this.schemaNamespace));
                }
                s.accept(p);
                taclets.addAll(p.getTopLevelTaclets());
                schemaNamespace = p.schemaVariables();
            }
            return taclets;
        }

        public Term getProblem() {
            // TODO weigl tbd
            return null;
        }
    }
}
