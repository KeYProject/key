module org.key_project.util {
    requires java.desktop;
    requires org.jspecify;

    exports org.key_project.util.bean;
    exports org.key_project.util.collection;
    exports org.key_project.util.bitops;
    exports org.key_project.util.helper;
    exports org.key_project.util.java;
    exports org.key_project.util.java.thread;
    exports org.key_project.util.lookup;
    exports org.key_project.util.reflection;
    exports org.key_project.util.testcategories;
    exports org.key_project.util;
}