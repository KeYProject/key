import org.jspecify.annotations.NullMarked;

/**
 * @author Alexander Weigl
 * @version 1 (6/18/25)
 */
@NullMarked
module key.testgen {
    exports de.uka.ilkd.key.testgen.smt.counterexample;
    exports de.uka.ilkd.key.testgen.macros;
    exports de.uka.ilkd.key.testgen.smt.testgen;
    exports de.uka.ilkd.key.testgen.settings;
    requires org.slf4j;
    requires key.core;
    requires key.prover;
    requires key.ncore;
    requires org.key_project.util;
    requires org.jspecify;
}