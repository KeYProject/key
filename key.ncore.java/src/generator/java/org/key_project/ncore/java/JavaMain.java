package org.key_project.ncore.java;

import com.github.javaparser.ParseProblemException;

import java.util.List;

/**
 *
 * @author Alexander Weigl
 * @version 1 (28.06.26)
 */
public class JavaMain {
    public static void main(String[] args) throws Exception {
        Generator gen = createJavaGenerator();
        try {
            gen.call();
        } catch (ParseProblemException ppe) {
            ppe.getProblems().forEach((it) -> System.err.format("%s: %s\n", it.getLocation(), it.getVerboseMessage()));
            throw ppe;
        }
    }

    private static Generator createJavaGenerator() {
        Generator gen = new Generator("key.ncore.java/src/adt/java-ast.java");

        gen.preSteps.add(new PreSteps.PreComputation());
        gen.addStep(new NodeSteps.SetPackage());
        gen.addStep(new NodeSteps.EnforceHierarchy());
        gen.addStep(new NodeSteps.ProcessFields());
        gen.addStep(new NodeSteps.AddAllFieldsConstructor());
        gen.addStep(new NodeSteps.addAllWoOptFieldsConstructor());
        gen.addStep(new NodeSteps.addCopyConstructor());
        gen.addStep(new NodeSteps.addMatch());
        gen.addStep(new NodeSteps.addWiths());
        gen.addStep(new NodeSteps.addBuilder());

        // weigl: this block adds the processing of
        // PROPERTY_* accessors and Node -> Map construction
        //addStep(new NodeSteps.addOverrideConstructor);
        //addStep(new NodeSteps.addOverrideConstructor2);
        //addStep(new NodeSteps.addGetProperties);
        //addStep(new NodeSteps.processFieldsAccessor);

        gen.addStep(new NodeSteps.addEquals());
        gen.addStep(new NodeSteps.ToString());
        gen.addStep(new NodeSteps.addHashCode());

        gen.addStep(new NodeSteps.handleRoot());

        var post = new PostSteps();
        gen.postSteps.add(post.new CreateVisitor());
        gen.postSteps.add(post.new CreateArgVisitor());
        gen.postSteps.add(post.new CreateVoidVisitor());
        gen.postSteps.add(post.new CreateTraversalVisitor());
        gen.postSteps.add(post.new CreateTraversalCopyOnDemandVisitor());
        return gen;
    }
}
