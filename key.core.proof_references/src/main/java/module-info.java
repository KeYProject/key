import org.jspecify.annotations.NullMarked;

/**
 *
 * @author Alexander Weigl 
 * @version 1 (31.03.24)
 */
@NullMarked
module key.core.proof_references {
    requires key.core;
    requires key.ncore;
    requires org.key_project.util;
    requires key.prover;
    requires org.jspecify;
}