package recoder.util;

/**
 * A progress listener listens to process events issued by algorithms.
 * 
 * @author AL
 * @since 0.72
 */
public interface ProgressListener {
    void workProgressed(ProgressEvent pe);
}