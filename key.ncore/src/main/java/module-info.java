import org.jspecify.annotations.NullMarked;

/**
 * @author Alexander Weigl
 * @version 1 (6/18/25)
 */
@NullMarked module key.ncore {
    requires org.jspecify;
    requires org.key_project.util;
    requires org.slf4j;

    exports org.key_project.logic;
    exports org.key_project.logic.op;
    exports org.key_project.logic.op.sv;
    exports org.key_project.logic.sort;
}
