/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.convenience;

import java.util.List;

import recoder.ModelElement;
import recoder.NamedModelElement;
import recoder.abstraction.Method;
import recoder.abstraction.ProgramModelElement;
import recoder.java.CompilationUnit;
import recoder.java.Identifier;
import recoder.java.ProgramElement;
import recoder.java.SourceElement;
import recoder.java.SourceElement.Position;
import recoder.java.reference.ReferencePrefix;
import recoder.kit.UnitKit;
import recoder.util.Debug;

/**
 * Create textual descriptions of program elements, program model elements or lists thereof. This
 * class is useful to create readable information for error reports, debugging or model browsers.
 *
 * @author AL, RN
 */
public class Format {

    /**
     * As a utility class, there is no need to create objects.
     */
    private Format() {
        super();
    }

    /**
     * Replaces tags in the format strings with information pieces about the given program element,
     * and returns it.
     * <TABLE>
     * <TR>
     * <TH>Tag</TH>
     * <TD>Replacement</TD>
     * </TR>
     * <TR>
     * <TH>%n</TH>
     * <TD>(Short) name of the entity, if available. Applies to named model elements, identifiers
     * and compilation units. For compilation units, returns the short name of the primary
     * type.</TD>
     * </TR>
     * <TR>
     * <TH>%N</TH>
     * <TD>Full name or path of the entity, if available. Applies to program model elements, named
     * reference prefixes, identifiers and compilation units; works as %n for all other named model
     * elements; methods have their signature attached using "%N" format; returns the canonical name
     * of a compilation unit (equals the long name of the primary type).</TD>
     * </TR>
     * <TR>
     * <TH>%m</TH>
     * <TD>Name of the entity, if available. Applies to named model elements, identifiers and
     * compilation units; works as "%n" except for methods, which have their signature attached
     * using "%N" format.</TD>
     * </TR>
     * <TR>
     * <TH>%s</TH>
     * <TD>Trimmed source code, if available. Applies only to source elements.</TD>
     * </TR>
     * <TR>
     * <TH>%c</TH>
     * <TD>Unqualified class name of the object.</TD>
     * </TR>
     * <TR>
     * <TH>%C</TH>
     * <TD>Fully qualified class name of the object.</TD>
     * </TR>
     * <TR>
     * <TH>%i</TH>
     * <TD>Object id as obtained by System.identityHashCode().</TD>
     * </TR>
     * <TR>
     * <TH>%p</TH>
     * <TD>Source line/column start position from last parsing, if available (only for source
     * elements).</TD>
     * </TR>
     * <TR>
     * <TH>%P</TH>
     * <TD>Source line/column start and end position from last parsing, if available (only for
     * source elements).</TD>
     * </TR>
     * <TR>
     * <TH>%r</TH>
     * <TD>Relative source line/column indentation, if available (only for source elements).</TD>
     * </TR>
     * <TR>
     * <TH>%u</TH>
     * <TD>Compilation unit, logical name, if available. Applies only to program elements that have
     * a compilation unit.</TD>
     * </TR>
     * <TR>
     * <TH>%f</TH>
     * <TD>File as obtained by DataLocation.getName(), if available. Applies only to program
     * elements that have a compilation unit associated with a file).</TD>
     * </TR>
     * </TABLE>
     * Any tag that does not apply does not produce an output (and is omitted, effectively).
     * <p>
     * Since 0.72, the method allows to use a single digit in front of each qualifier, which
     * controls minimum indentation. The digit is used for <CODE>%p</CODE>,<CODE>%P</CODE>, and
     * <CODE>%r</CODE>.
     *
     * @param formatText the format text, containing tags.
     * @param e the model element to be formatted.
     * @return a textual representation of the model element.
     */
    public static String toString(String formatText, ModelElement e) {
        Debug.assertNonnull(formatText);
        StringBuffer res = new StringBuffer();
        int len = formatText.length();
        for (int i = 0; i < len; i += 1) {
            char c = formatText.charAt(i);
            if (c != '%' || i == len - 1) {
                res.append(c);
            } else {
                int columns = 1;
                i += 1;
                c = formatText.charAt(i);
                if (c >= '0' && c <= '9' && i < len - 1) {
                    columns = Math.max(1, c - '0');
                    i += 1;
                    c = formatText.charAt(i);
                }
                switch (c) {
                case 'n':
                    if (e instanceof NamedModelElement) {
                        res.append(((NamedModelElement) e).getName());
                    } else if (e instanceof Identifier) {
                        res.append(((Identifier) e).getText());
                    } else if (e instanceof CompilationUnit) {
                        res.append(((CompilationUnit) e).getPrimaryTypeDeclaration().getName());
                    }
                    break;
                case 'N':
                    if (e instanceof NamedModelElement) {
                        if (e instanceof ProgramModelElement) {
                            res.append(((ProgramModelElement) e).getFullName());
                            if (e instanceof Method) {
                                res.append(toString("%N", ((Method) e).getSignature()));
                            }
                        } else if (e instanceof ReferencePrefix) {
                            res.append(Naming.toPathName((ReferencePrefix) e));
                        } else {
                            res.append(((NamedModelElement) e).getName());
                        }
                    } else if (e instanceof Identifier) {
                        res.append(((Identifier) e).getText());
                    } else if (e instanceof CompilationUnit) {
                        res.append(Naming.toCanonicalName((CompilationUnit) e));
                    }
                    break;
                case 'm':
                    if (e instanceof NamedModelElement) {
                        res.append(((NamedModelElement) e).getName());
                        if (e instanceof Method) {
                            res.append(toString("%N", ((Method) e).getSignature()));
                        }
                    } else if (e instanceof Identifier) {
                        res.append(((Identifier) e).getText());
                    } else if (e instanceof CompilationUnit) {
                        res.append(((CompilationUnit) e).getPrimaryTypeDeclaration().getName());
                    }
                    break;
                case 's':
                    if (e instanceof SourceElement) {
                        res.append(((SourceElement) e).toSource().trim());
                    }
                    break;
                case 'c':
                    if (e == null) {
                        res.append("null");
                    } else {
                        String name = e.getClass().getName();
                        res.append(name.substring(name.lastIndexOf('.') + 1));
                    }
                    break;
                case 'C':
                    if (e == null) {
                        res.append("null");
                    } else {
                        res.append(e.getClass().getName());
                    }
                    break;
                case 'i':
                    if (e != null) {
                        int id = System.identityHashCode(e);
                        if (id < 0) {
                            res.append(Long.toString((long) (id & 0x7FFFFFFF) | 0x80000000L, 16));
                        } else {
                            res.append(Integer.toString(id, 16));
                        }
                    }
                    break;
                case 'p':
                    if (e instanceof SourceElement) {
                        SourceElement se = (SourceElement) e;
                        se = se.getFirstElement();
                        if (se != null) {
                            append(se.getStartPosition(), columns, res);
                        }
                    }
                    break;
                case 'P':
                    if (e instanceof SourceElement) {
                        SourceElement se = (SourceElement) e;
                        SourceElement se2 = se.getFirstElement();
                        if (se2 != null) {
                            append(se2.getStartPosition(), columns, res);
                            res.append('-');
                            se2 = se.getLastElement();
                            append(se2.getEndPosition(), columns, res);
                        }
                    }
                    break;
                case 'r':
                    if (e instanceof SourceElement) {
                        SourceElement se = (SourceElement) e;
                        se = se.getFirstElement();
                        if (se != null) {
                            append(se.getRelativePosition(), columns, res);
                        }
                    }
                    break;
                case 'u':
                    if (e instanceof ProgramElement) {
                        CompilationUnit cu = UnitKit.getCompilationUnit((ProgramElement) e);
                        if (cu != null) {
                            res.append(Naming.toCanonicalName(cu));
                        }
                    }
                    break;
                case 'f':
                    if (e instanceof ProgramElement) {
                        CompilationUnit cu = UnitKit.getCompilationUnit((ProgramElement) e);
                        if (cu != null) {
                            res.append(cu.getDataLocation());
                        }
                    }
                    break;
                default:
                    res.append('%').append(c);
                    break;
                }
            }
        }
        return res.toString();
    }

    private static void append(Position pos, int columns, StringBuffer buf) {
        int k = 1;
        for (int i = columns; i > 1; i -= 1, k *= 10) {
        }
        int line = -1;
        int col = -1;
        if (pos != Position.UNDEFINED) {
            line = pos.getLine();
            col = pos.getColumn();
        }
        for (int j = Math.max(1, line); j < k; j *= 10) {
            buf.append(' ');
        }
        if (line == -1) {
            buf.append('?');
        } else {
            buf.append(line);
        }
        buf.append('/');
        for (int j = Math.max(1, col); j < k; j *= 10) {
            buf.append(' ');
        }
        if (col == -1) {
            buf.append('?');
        } else {
            buf.append(col);
        }
    }

    /**
     * Formats a list of model elements. Each element is formatted according to the format string by
     * a call to {@link #toString(String, String, String, String, ModelElementList)}using
     * <CODE>"(", ", ", ")"</CODE> formatting.
     *
     * @param formatText the format text, containing tags.
     * @param l the list to be formatted.
     * @return a textual representation of the list.
     * @see #toString(String, String, String, String, ModelElementList)
     */
    public static String toString(String formatText, List<? extends ModelElement> l) {
        return toString(formatText, "(", ", ", ")", l);
    }

    /**
     * Formats a list of model elements. Each element is formatted according to the format string,
     * surrounded by the header/footer and each inner element is followed by a separator.
     *
     * @param formatText the format text, containing tags.
     * @param header the list start.
     * @param separator the element separator.
     * @param footer the list start.
     * @param l the list to be formatted.
     * @return a textual representation of the list.
     * @since 0.72
     */
    public static String toString(String formatText, String header, String separator, String footer,
            List<? extends ModelElement> l) {
        if (l == null) {
            return null;
        }
        StringBuilder sb = new StringBuilder(64);
        sb.append(header);
        int s = l.size();
        if (s > 0) {
            sb.append(toString(formatText, l.get(0)));
            for (int i = 1; i < s; i++) {
                sb.append(separator);
                sb.append(toString(formatText, l.get(i)));
            }
        }
        sb.append(footer);
        return sb.toString();
    }

    /**
     * Formats a source element using a default format. The default format string is <CODE>"\"%s\"
     *
     * &#64;param se the source element to be formatted.
     * &#64;return a textual representation of the source element.
     * &#64;%p [%f]"</CODE>.
     */
    public static String toString(ProgramElement se) {
        return toString("\"%s\" @%p [%f]", se);
    }

    /**
     * Formats a program element list using a default format. The default format string is
     * <CODE>"\"%s\"
     *
     * &#64;param l the list to be formatted.
     * &#64;return a textual representation of the list.
     * &#64;%p"</CODE>.
     */
    public static String toString(List<? extends ModelElement> l) {
        return toString("\"%s\" @%p", l);
    }
}
