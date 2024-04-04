/**
 *
 * @author Alexander Weigl
 * @version 1 (04.04.24)
 */
module org.key_project.core.testgen {
    requires org.key_project.core;
    requires org.slf4j;
    requires org.key_project.util;
    requires org.key_project.ncore;
    requires org.jspecify;
    exports de.uka.ilkd.key.testgen.smt.testgen;
    exports de.uka.ilkd.key.testgen.macros;
    exports de.uka.ilkd.key.testgen.smt.counterexample;
    exports de.uka.ilkd.key.testgen.settings;
}