import de.uka.ilkd.key.proof.init.POExtension;
import de.uka.ilkd.key.symbolic_execution.po.TruthValuePOExtension;

import org.jspecify.annotations.NullMarked;

/**
 *
 * @author Alexander Weigl
 * @version 1 (31.03.24)
 */
@NullMarked module key.core.symbolic_execution {
    exports de.uka.ilkd.key.symbolic_execution;
    exports de.uka.ilkd.key.symbolic_execution.model;
    exports de.uka.ilkd.key.symbolic_execution.po;
    exports de.uka.ilkd.key.symbolic_execution.profile;
    exports de.uka.ilkd.key.symbolic_execution.strategy;
    exports de.uka.ilkd.key.symbolic_execution.strategy.breakpoint;
    exports de.uka.ilkd.key.symbolic_execution.util;

    requires java.xml;
    requires key.core;
    requires key.ncore;
    requires org.key_project.util;
    requires java.desktop;
    requires org.slf4j;
    requires org.jspecify;
    requires key.prover;
    requires org.checkerframework.checker.qual;

    provides POExtension with TruthValuePOExtension;
}
