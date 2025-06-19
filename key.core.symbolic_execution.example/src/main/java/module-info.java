import org.jspecify.annotations.NullMarked;

/**
 *
 * @author Alexander Weigl
 * @version 1 (31.03.24)
 */
@NullMarked module key.core.symbolic_execution.example {
    requires transitive key.core.symbolic_execution;
    requires key.core;
    requires org.key_project.util;
    requires org.slf4j;
    requires org.jspecify;
    requires key.prover;
}
