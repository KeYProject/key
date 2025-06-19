import org.jspecify.annotations.NullMarked;

/**
 * @author Alexander Weigl
 * @version 1 (6/18/25)
 */
@NullMarked
module key.prover {
    exports org.key_project.prover.sequent;
    exports org.key_project.prover.rules;
    exports org.key_project.prover.proof;
    exports org.key_project.prover.proof.rulefilter;
    exports org.key_project.prover.strategy;
    exports org.key_project.prover.engine;
    exports org.key_project.prover.rules.conditions;
    exports org.key_project.prover.rules.tacletbuilder;
    exports org.key_project.prover.strategy.costbased;
    exports org.key_project.prover.engine.impl;
    exports org.key_project.prover.strategy.costbased.feature;
    exports org.key_project.prover.rules.instantiation;
    exports org.key_project.prover.rules.instantiation.caches;
    exports org.key_project.prover.rules.matcher.vm.instruction;
    exports org.key_project.prover.strategy.costbased.termProjection;
    exports org.key_project.prover.strategy.costbased.termfeature;
    exports org.key_project.prover.strategy.costbased.termgenerator;
    exports org.key_project.prover.strategy.costbased.feature.instantiator;
    exports org.key_project.prover.rules.matcher.vm;
    requires key.ncore;
    requires org.key_project.util;
    requires org.jspecify;
    requires org.checkerframework.checker.qual;
    requires org.slf4j;
}