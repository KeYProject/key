import org.jspecify.annotations.NullMarked;

/**
 *
 * @author Alexander Weigl
 * @version 1 (31.03.24)
 */
@NullMarked module key.core.rifl {
    exports de.uka.ilkd.key.util.rifl;

    requires key.core;
    requires key.recoder;
    requires java.xml;
    requires org.slf4j;
    requires org.key_project.util;
    requires org.jspecify;
}
