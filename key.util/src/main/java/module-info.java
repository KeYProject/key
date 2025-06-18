/**
 * @author Alexander Weigl
 * @version 1 (6/18/25)
 */
module org.key_project.util {
    exports org.key_project.util.collection;
    exports org.key_project.util;
    exports org.key_project.util.java;
    exports org.key_project.util.lookup;
    exports org.key_project.util.bitops;
    exports org.key_project.util.reflection;
    exports org.key_project.util.helper;
    requires java.desktop;
    requires org.jspecify;
    requires org.checkerframework.checker.qual;
    requires org.slf4j;
    requires org.checkerframework.checker.util;
}