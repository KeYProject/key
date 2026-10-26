package java.util.function;

/**
 * Minimal boot stub of {@code java.util.function.Function} (SAM {@code apply}),
 * used as a resolution target for lambdas and method references.
 *
 * <p>JavaRedux follows JDK semantics: referential and functional interfaces keep their
 * type parameters so that JavaParser can map them (e.g. {@code Function<String, Integer>})
 * during lambda desugaring. KeY's Java model erases type variables to their upper bound.</p>
 *
 * @param <T> the input type
 * @param <R> the result type
 */
public interface Function<T, R> {

    R apply(T arg0);
}
