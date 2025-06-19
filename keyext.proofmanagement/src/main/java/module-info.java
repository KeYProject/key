import org.jspecify.annotations.NullMarked;

/**
 *
 * @author Alexander Weigl 
 * @version 1 (31.03.24)
 */
@NullMarked
module keyext.proofmanagement {
    requires key.core;
    requires org.key_project.util;
    requires key.ncore;
    requires freemarker;
    requires java.datatransfer;
    requires java.desktop;
    requires key.ui;
    requires org.slf4j;
    requires org.jspecify;
}