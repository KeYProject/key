package java.util.function;

/**
 * Minimal boot stub of {@code java.util.function.Predicate} (SAM {@code test}),
 * used as a resolution target for lambdas and method references.
 *
 * <p>JavaRedux follows JDK semantics: referential and functional interfaces keep their
 * type parameters so that JavaParser can map them (e.g. {@code Predicate<String>})
 * during lambda desugaring. KeY's Java model erases type variables to their upper bound.</p>
 *
 * @param <T> the input type
 */
public interface Predicate<T> {

    boolean test(T arg0);
}
