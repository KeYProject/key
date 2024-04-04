import de.uka.ilkd.key.proof.init.DefaultProfileResolver;
import de.uka.ilkd.key.proof.init.POExtension;
import de.uka.ilkd.key.symbolic_execution.po.TruthValuePOExtension;
import de.uka.ilkd.key.symbolic_execution.profile.SymbolicExecutionJavaProfileDefaultProfileResolver;

/**
 *
 * @author Alexander Weigl
 * @version 1 (31.03.24)
 */
module org.key_project.symbolic_execution{exports de.uka.ilkd.key.symbolic_execution;exports de.uka.ilkd.key.symbolic_execution.model;exports de.uka.ilkd.key.symbolic_execution.po;exports de.uka.ilkd.key.symbolic_execution.profile;exports de.uka.ilkd.key.symbolic_execution.strategy;exports de.uka.ilkd.key.symbolic_execution.strategy.breakpoint;exports de.uka.ilkd.key.symbolic_execution.util;requires java.xml;requires org.key_project.core;requires org.key_project.ncore;requires org.key_project.util;requires java.desktop;requires org.slf4j;requires org.jspecify;

provides DefaultProfileResolver with SymbolicExecutionJavaProfileDefaultProfileResolver;provides POExtension with TruthValuePOExtension;}
