/**
 *
 * @author Alexander Weigl
 * @version 1 (3/22/26)
 */
module key.core.infflow {
    exports de.uka.ilkd.key.informationflow.macros;
    exports de.uka.ilkd.key.informationflow.impl;
    requires key.core;
    requires key.ncore;
    requires key.prover;
    requires org.jspecify;
    requires org.key_project.util;
    requires org.slf4j;
}