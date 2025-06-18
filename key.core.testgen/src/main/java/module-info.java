/**
 * @author Alexander Weigl
 * @version 1 (6/18/25)
 */
module org.key_project.testgen {
    exports de.uka.ilkd.key.testgen.smt.counterexample;
    exports de.uka.ilkd.key.testgen.macros;
    exports de.uka.ilkd.key.testgen.smt.testgen;
    exports de.uka.ilkd.key.testgen.settings;
    requires org.slf4j;
    requires org.key_project.core;
    requires org.key_project.prover;
    requires org.key_project.ncore;
    requires org.key_project.util;
    requires org.jspecify;
}