package org.key_project.ncore.java;

import com.github.javaparser.ParseProblemException;

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
        gen.addStep(new NodeSteps.SetPackage());
        gen.addStep(new NodeSteps.EnforceHierarchy("BaseAstNode"));
        gen.addStep(new NodeSteps.ProcessFields());
        gen.addStep(new NodeSteps.addAllWoOptFieldsConstructor());
        gen.addStep(new NodeSteps.addAllWoOptFieldsConstructor());
        gen.addStep(new NodeSteps.addCopyConstructor());
        //gen.addStep(new NodeSteps.addMatch());
        gen.addStep(new NodeSteps.addWiths());
        gen.addStep(new NodeSteps.addBuilder());

        // weigl: this block adds the processing of
        // PROPERTY_* accessors and Node -> Map construction
        //addStep(NodeSteps::addOverrideConstructor);
        //addStep(NodeSteps::addOverrideConstructor2);
        //addStep(NodeSteps::addGetProperties);
        //addStep(NodeSteps::processFieldsAccessor);

        gen.addStep(new NodeSteps.addEquals());
        gen.addStep(new NodeSteps.ToString());
        gen.addStep(new NodeSteps.addHashCode());

        gen.addStep(new NodeSteps.handleRoot());

        gen.postSteps.add(PostSteps::createVisitor);
        gen.postSteps.add(PostSteps::createArgVisitor);
        gen.postSteps.add(PostSteps::createVoidVisitor);
        gen.postSteps.add(PostSteps::createTraversalVisitor);
        gen.postSteps.add(PostSteps::createTraversalCopyOnDemandVisitor);
        gen.postSteps.add(PostSteps::createDeepCopyVisitor);

        return gen;
    }

}
