package org.key_project.java.ast;

import com.github.javaparser.ast.Node;

/**
 * A key to a piece of data associated with a {@link Node} at runtime.
 * The key contains type information that can be used to check the
 * type of any user data value for the key when the value is set. DataKey is abstract in order to
 * force the creation of a subtype. That subtype is used to test for identity when looking for the
 * user data because actual object identity would suffer from problems under serialization.
 * So, the correct way to declare a DataKey is like this:
 * <p>
 * <pre>
 * {@code
 * public static final DataKey<Role> ROLE = new DataKey<Role>() { };
 * }
 * </pre>
 * <p>
 * This code was taken from the <a href="http://wicket.apache.org/">Wicket project</a>.
 *
 * @param <T> The type of the object which is stored
 * @see Node#getData(com.github.javaparser.ast.DataKey)
 */
public record Property<T>(String name) {
}
