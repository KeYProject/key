/**
 * A package to pretty-print information using line breaks and
 * indentation. For instance, it can be used to print
 *
 * <pre>
 * while (i > 0) {
 *     i--;
 *     j++;
 * }
 * </pre>
 *
 * instead of
 *
 * <pre>
 * while (i > 0) {
 *     i--;
 *     j++;
 * }
 * </pre>
 *
 * if a maximum line width of 15 characters is chosen. The frontend
 * to the Pretty-Printer is the {@link
 * de.uka.ilkd.key.util.pp.Layouter} class. You may configure what
 * happens with the output by implemenenting the {@link
 * de.uka.ilkd.key.util.pp.Backend} interface, or by using the
 * standard implementation {@link
 * de.uka.ilkd.key.util.pp.StringBackend}.
 *
 * @author Martin Giese
 */
package de.uka.ilkd.key.util.pp;
