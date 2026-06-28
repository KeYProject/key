package org.key_project.ncore.java;

import com.github.javaparser.ParseProblemException;

import java.util.List;

/**
 *
 * @author Alexander Weigl
 * @version 1 (28.06.26)
 */
public class KeyMain {
    public static void main(String[] args) throws Exception {
        Generator gen = createKeyGenerator();
        try {
            gen.call();
        } catch (ParseProblemException ppe) {
            ppe.getProblems().forEach((it) -> System.err.format("%s: %s\n", it.getLocation(), it.getVerboseMessage()));
            throw ppe;
        }
    }

    private static Generator createKeyGenerator() {
        Generator gen = new Generator(
                "key.ncore.java/src/adt/key-ast.java"
        );
        gen.preSteps.add(new PreSteps.PreComputation());
        gen.addStep(new NodeSteps.SetPackage("org.key_project.key.ast"));
        gen.addStep(new NodeSteps.EnforceHierarchy("BaseAstNode"));
        gen.addStep(new NodeSteps.ProcessFields(false));
        gen.addStep(new NodeSteps.AddAllFieldsConstructor());
        gen.addStep(new NodeSteps.addAllWoOptFieldsConstructor());
        gen.addStep(new NodeSteps.addCopyConstructor());
        //gen.addStep(new NodeSteps.addMatch());
        //gen.addStep(new NodeSteps.addWiths());
        gen.addStep(new NodeSteps.addBuilder());

        // weigl: this block adds the processing of
        // PROPERTY_* accessors and Node -> Map construction
        //addStep(NodeSteps::addOverrideConstructor);
        //addStep(NodeSteps::addOverrideConstructor2);
        //addStep(NodeSteps::addGetProperties);
        //addStep(NodeSteps::processFieldsAccessor);

        gen.addStep(new NodeSteps.addEquals());
        gen.addStep(new NodeSteps.ToString());
        gen.addStep(new NodeSteps.addHashCode(false));

        gen.addStep(new NodeSteps.handleRoot());

        var post = new PostSteps();
        post.name = "org.key_project.key.ast.visitor";
        post.imports = List.of("org.key_project.key.ast.visitor.*",
                "org.key_project.key.ast.*",
                "java.util.*");
        post.listClass = "List";
        post.topClass = "AstNode";
        gen.postSteps.add(post.new CreateVisitor());
        gen.postSteps.add(post.new CreateArgVisitor());
        gen.postSteps.add(post.new CreateVoidVisitor());
        gen.postSteps.add(post.new CreateTraversalVisitor());
        gen.postSteps.add(post.new CreateTraversalCopyOnDemandVisitor());
        return gen;
    }

}
