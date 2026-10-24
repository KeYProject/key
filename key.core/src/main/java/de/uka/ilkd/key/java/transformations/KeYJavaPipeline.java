/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.transformations;

import java.net.URI;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.java.transformations.pipeline.*;
import de.uka.ilkd.key.java.transformations.pipeline.lambda.LambdaReplacer;

import com.github.javaparser.ast.CompilationUnit;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * @author Alexander Weigl
 * @version 1 (11/7/21)
 */
public class KeYJavaPipeline {
    private final TransformationPipelineServices pipelineServices;
    private final List<JavaTransformer> steps = new LinkedList<>();
    private static final Logger LOGGER = LoggerFactory.getLogger(KeYJavaPipeline.class);


    public KeYJavaPipeline(TransformationPipelineServices pipelineServices) {
        this.pipelineServices = pipelineServices;
    }

    public TransformationPipelineServices getPipelineServices() {
        return pipelineServices;
    }

    public List<JavaTransformer> getSteps() {
        return steps;
    }

    public static KeYJavaPipeline createDefault(TransformationPipelineServices pipelineServices) {
        KeYJavaPipeline p = new KeYJavaPipeline(pipelineServices);
        p.add(new TextblockTransformer());
        p.add(new MultiCatchReducer());
        p.add(new TryWithResourceReducer());
        p.add(new EnumClassBuilder(pipelineServices));
        p.add(new RecordClassBuilder(pipelineServices));
        // Lambdas and method references must be eliminated before any JML processing:
        // (i) JP2KeYConverter rejects both, and (ii) the JML model-method conversion of
        // the generated classes (phase 2) requires JMLTransformer to run afterwards.
        p.add(new LambdaReplacer(pipelineServices));
        // Hoists the local classes created by the lambda replacer (and user-written local
        // classes) into unique private static final nested classes capturing the closure.
        p.add(new LocalClassTransformation(pipelineServices));
        // Converts the JML contracts of lambdas and method references (extracted by the
        // LambdaReplacer) into model methods on the desugared classes (Csiky Def. 7/8). Runs
        // after the hoisting so that the clause bodies can refer to the hoisted fields.
        p.add(new LambdaContractModelMethods(pipelineServices));
        p.add(new JMLTransformer(pipelineServices));
        p.add(new JmlDocRemoval(pipelineServices));
        p.add(new ImplicitFieldAdder(pipelineServices));
        p.add(new InstanceAllocationMethodBuilder(pipelineServices));
        p.add(new ConstructorNormalformBuilder(pipelineServices));
        p.add(new ClassPreparationMethodBuilder(pipelineServices));
        p.add(new ClassInitializeMethodBuilder(pipelineServices));
        p.add(new PrepareObjectBuilder(pipelineServices));
        p.add(new CreateBuilder(pipelineServices));
        p.add(new CreateObjectBuilder(pipelineServices));
        // Below is an expensive transformation as it has to traverse down
        // to an expression level.
        p.add(new ConstantStringExpressionEvaluator(pipelineServices));
        return p;
    }

    public void add(JavaTransformer step) {
        steps.add(step);
    }

    public void apply() {
        apply(pipelineServices.getCache().getUnits());
    }

    public void apply(Collection<CompilationUnit> compilationUnits) {
        for (CompilationUnit compilationUnit : compilationUnits) {
            URI resource = compilationUnit.getStorage()
                    .map(it -> it.getPath().toUri())
                    .orElse(null);

            for (JavaTransformer step : steps) {
                long start = System.currentTimeMillis();
                step.apply(compilationUnit);
                long stop = System.currentTimeMillis();
                LOGGER.debug("Processed {} on {} ms: {}",
                    step.getClass().getSimpleName(), resource, stop - start);
            }
        }
    }
}
