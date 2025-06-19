import org.jspecify.annotations.NullMarked;

/**
 *
 * @author Alexander Weigl 
 * @version 1 (31.03.24)
 */
@NullMarked
module keyext.ui.testgen {
    requires key.ui;
    requires java.desktop;
    requires org.slf4j;
    requires key.core;
    requires key.prover;
    requires key.testgen;
    requires org.jspecify;
}