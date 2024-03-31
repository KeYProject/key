import de.uka.ilkd.key.proof.init.POExtension;
import de.uka.ilkd.key.symbex.po.TruthValuePOExtension;

/**
 *
 * @author Alexander Weigl 
 * @version 1 (31.03.24)
 */
module org.key_project.symbolic_execution {
    exports de.uka.ilkd.key.symbex;
    exports de.uka.ilkd.key.symbex.model;
    exports de.uka.ilkd.key.symbex.po;
    exports de.uka.ilkd.key.symbex.profile;
    exports de.uka.ilkd.key.symbex.strategy;
    exports de.uka.ilkd.key.symbex.strategy.breakpoint;
    exports de.uka.ilkd.key.symbex.util;
    requires java.xml;
    requires org.key_project.core;
    requires org.key_project.ncore;
    requires org.key_project.util;
    requires java.desktop;
    requires org.slf4j;
    requires org.jspecify;

    provides POExtension with TruthValuePOExtension;
}