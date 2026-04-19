/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.ncore.java;

import com.github.javaparser.ParseProblemException;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.utils.SourceRoot;
import org.key_project.ncore.java.NodeSteps.NodeStep;
import org.key_project.ncore.java.PostSteps.PostStep;
import org.key_project.ncore.java.PreSteps.PreStep;

import java.io.File;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.Callable;
import java.util.stream.Stream;

/**
 *
 * @author Alexander Weigl
 * @version 1 (4/11/26)
 */
public class Generator implements Callable<Integer> {
    public static final Path ROOT = Paths.get("key.ncore.java/src/generated/java");
    public static final Generator INSTANCE = new Generator();

    CompilationUnit metaModel;

    List<NodeStep> nodeSteps = new ArrayList<>(64);
    List<PreStep> preSteps = new ArrayList<>(64);
    List<PostStep> postSteps = new ArrayList<>(64);

    public static void main(String[] args) throws Exception {
        INSTANCE.call();
    }

    public Generator() {
        preSteps.add(new PreSteps.PreComputation());

        addStep(NodeSteps::setPackage);
        addStep(NodeSteps::processFields);
        addStep(NodeSteps::addAllFieldsConstructor);
        addStep(NodeSteps::addAllWoOptFieldsConstructor);
        addStep(NodeSteps::addCopyConstructor);
        addStep(NodeSteps::addEquals);
        addStep(NodeSteps::ToString);
        addStep(NodeSteps::addHashCode);
        addStep(NodeSteps::addWiths);
        addStep(NodeSteps::addBuilder);
        addStep(NodeSteps::addOverrideConstructor);
        addStep(NodeSteps::addOverrideConstructor2);
        addStep(NodeSteps::addGetProperties);
        addStep(NodeSteps::processFieldsAccessor);

        postSteps.add(PostSteps::createVisitor);
        postSteps.add(PostSteps::createArgVisitor);
        postSteps.add(PostSteps::createVoidVisitor);
        postSteps.add(PostSteps::createTraversalVisitor);
        postSteps.add(PostSteps::createDeepCopyVisitor);
    }

    private void addStep(NodeStep nodeStep) {
        nodeSteps.add(nodeStep);
    }

    @SuppressWarnings("unchecked")
    <T> T getStep(Class<T> step) {
        return (T) Stream.concat(preSteps.stream(), postSteps.stream())
                .filter(step::isInstance)
                .findFirst()
                .orElse(null);
    }

    @Override
    public Integer call() throws Exception {
        var config = new ParserConfiguration();
        config.setStoreTokens(false);
        config.setLexicalPreservationEnabled(false);
        config.setLanguageLevel(ParserConfiguration.LanguageLevel.JAVA_25);

        StaticJavaParser.setConfiguration(config);
        metaModel = StaticJavaParser
                .parse(new File("key.ncore.java/src/adt/java-ast.java").getAbsoluteFile());
        Files.createDirectories(ROOT);
        SourceRoot sourceRoot = new SourceRoot(ROOT);

        final var types = metaModel.getTypes();
        for (var nodeStep : preSteps) {
            nodeStep.applyOn(types);
        }

        List<CompilationUnit> nodeUnits = new ArrayList<>(types.size());
        for (var type : types) {
            var cu = new CompilationUnit();
            cu.addType(type);
            metaModel.getImports().forEach(it -> cu.addImport(it.clone()));
            metaModel.addImport("java.lang.Objects");
            metaModel.addImport("java.util.*");

            for (var nodeStep : nodeSteps) {
                nodeStep.applyOn((ClassOrInterfaceDeclaration) type);
            }

            nodeUnits.add(cu);
            sourceRoot.add(cu);
        }

        for (var nodeStep : postSteps) {
            nodeStep.applyOn(nodeUnits, sourceRoot);
        }

        sourceRoot.saveAll();
        return 0;
    }


}
