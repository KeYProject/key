/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package edu.kit.iti.formal.astgen;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;

import de.uka.ilkd.key.nparser.AstgenBaseVisitor;
import de.uka.ilkd.key.nparser.AstgenLexer;
import de.uka.ilkd.key.nparser.AstgenParser;

import com.palantir.javapoet.ClassName;
import com.palantir.javapoet.ParameterizedTypeName;
import com.palantir.javapoet.TypeName;
import edu.kit.iti.formal.astgen.gen.HierarchyRunner;
import edu.kit.iti.formal.astgen.gen.NodeRunner;
import edu.kit.iti.formal.astgen.model.Attr;
import edu.kit.iti.formal.astgen.model.Hierarchy;
import edu.kit.iti.formal.astgen.model.Node;
import edu.kit.iti.formal.astgen.model.NodeWrapper;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.DiagnosticErrorListener;

/**
 * @author Alexander Weigl
 * @version 1 (10.09.17)
 */
public class Astgen {
    private Hierarchy hierarchy;

    private Path hierarchyFile;

    private Path sourceFolder;

    public static void main(String[] args) throws IOException {
        Astgen astgen = new Astgen();
        astgen.setHierarchyFile(Paths.get(args[0]));
        astgen.setSourceFolder(Paths.get(args[1]));
        astgen.run();
    }

    public void run() throws IOException {
        setHierarchy(loadHierarchyFile());

        Files.createDirectories(sourceFolder);

        NodeRunner nodeRunner = new NodeRunner();
        nodeRunner.setHierarchy(getHierarchy());
        nodeRunner.setSourceDirectory(getSourceFolder());
        nodeRunner.run();

        HierarchyRunner hierarchyRunner = new HierarchyRunner();
        hierarchyRunner.setHierarchy(hierarchy);
        hierarchyRunner.setSourceDirectory(getSourceFolder());
        hierarchyRunner.run();
    }

    private Hierarchy loadHierarchyFile() throws IOException {
        var lexer = new AstgenLexer(CharStreams.fromPath(getHierarchyFile()));
        var parser = new AstgenParser(new CommonTokenStream(lexer));
        parser.addErrorListener(new DiagnosticErrorListener());
        var ctx = parser.file();
        var builder = new HierarchyBuilderVisitor();
        ctx.accept(builder);
        return builder.hierarchy;
    }

    private static class HierarchyBuilderVisitor extends AstgenBaseVisitor<Object> {
        private Hierarchy hierarchy;
        private String currentPackage;

        @Override
        public Object visitFile(AstgenParser.FileContext ctx) {
            var mainPackage = visitIdent(ctx.packageClause().ident());
            this.hierarchy = new Hierarchy(mainPackage, new ArrayList<>());
            super.visitFile(ctx);

            Map<String, Node> nodes = new HashMap<>();
            for (Node node : hierarchy.nodes()) {
                nodes.put(node.name(), node);
            }

            for (var nctx : ctx.command()) {
                var n = nctx.astNode();
                if (n == null)
                    continue;
                var node = nodes.get(visitIdent(n.ident()));
                var extendz = visitIdent(n.extendsClause().ident());
                Node superclass = Objects.requireNonNull(nodes.get(extendz),
                    "Node not found by name " + extendz);
                node.extendz().setNode(superclass);
                superclass.children().add(node);

                for (var inter : n.implementsClause().ident()) {
                    var i = visitIdent(inter);
                    node.extendz().setNode(
                        Objects.requireNonNull(nodes.get(i),
                            "Node not found by name " + i));
                }
            }
            return this.hierarchy;
        }

        @Override
        public Object visitPackageClause(AstgenParser.PackageClauseContext ctx) {
            this.currentPackage = visitIdent(ctx.ident());
            return this.currentPackage;
        }

        @Override
        public Node visitAstNode(AstgenParser.AstNodeContext ctx) {
            var node = new Node(currentPackage, visitIdent(ctx.ident()),
                new NodeWrapper(), new ArrayList<>(),
                ctx.ABSTRACT() != null,
                ctx.FINAL() != null,
                new ArrayList<>(),
                ctx.field().stream().map(this::visitField).toList(),
                "");
            hierarchy.nodes().add(node);
            return node;
        }

        @Override
        public String visitExtendsClause(AstgenParser.ExtendsClauseContext ctx) {
            return visitIdent(ctx.ident());
        }

        @Override
        public List<String> visitImplementsClause(AstgenParser.ImplementsClauseContext ctx) {
            return ctx.i.stream().map(this::visitIdent).toList();
        }

        @Override
        public Attr visitField(AstgenParser.FieldContext ctx) {
            var typename = visitIdent(ctx.type);
            boolean isMulti = ctx.islist != null;
            var type = switch (typename) {
            case "int" -> TypeName.INT;
            case "bool" -> TypeName.BOOLEAN;
            case "short" -> TypeName.SHORT;
            case "long" -> TypeName.LONG;
            case "double" -> TypeName.DOUBLE;
            case "byte" -> TypeName.BYTE;
            case "char" -> TypeName.CHAR;
            case "float" -> TypeName.FLOAT;
            default -> ClassName.bestGuess(typename);
            };
            if (isMulti) {
                type = ParameterizedTypeName.get(ClassName.get(List.class), type);
            }

            return new Attr(visitIdent(ctx.name), type,
                ctx.isnullable != null, isMulti, ctx.javadoc().getText());
        }

        @Override
        public String visitIdent(AstgenParser.IdentContext ctx) {
            return ctx.getText();
        }
    }

    public Hierarchy getHierarchy() {
        return hierarchy;
    }

    public void setHierarchy(Hierarchy hierarchy) {
        this.hierarchy = hierarchy;
    }

    public Path getHierarchyFile() {
        return hierarchyFile;
    }

    public void setHierarchyFile(Path hierarchyFile) {
        this.hierarchyFile = hierarchyFile;
    }

    public Path getSourceFolder() {
        return sourceFolder;
    }

    public void setSourceFolder(Path sourceFolder) {
        this.sourceFolder = sourceFolder;
    }
}
