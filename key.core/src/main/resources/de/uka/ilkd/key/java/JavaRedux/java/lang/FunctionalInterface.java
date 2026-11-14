package java.lang;

/**
 * Minimal boot stub of {@code java.lang.FunctionalInterface}.
 *
 * <p>KeY's Java-model builder cannot load annotation declarations as boot classes (the
 * Recoder/JP2KeYConverter path rejects {@code @interface} declarations, see
 * {@code coverage/rejected/annotation-declaration}), so this stub is a plain interface.
 * JavaParser's symbol solver only resolves the annotation by name
 * ({@code AstResolutionUtils.hasDirectlyAnnotation} / {@code FunctionalInterfaceLogic}), which
 * succeeds regardless of the declaration kind.</p>
 */
public interface FunctionalInterface {
}
