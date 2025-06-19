import org.jspecify.annotations.NullMarked;

/**
 *
 * @author Alexander Weigl 
 * @version 1 (31.03.24)
 */
@NullMarked
module keyext.removegenerics {
    requires key.recoder;
    requires org.slf4j;
    requires org.jspecify;
}