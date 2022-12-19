package de.uka.ilkd.key.java;

import java.io.IOException;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.util.Debug;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import recoder.service.KeYCrossReferenceSourceInfo;

/**
 * Top level implementation of a Java {@link ProgramElement}. taken from COMPOST and changed to
 * achieve an immutable structure
 */
public abstract class JavaProgramElement extends JavaSourceElement implements ProgramElement {
    public static final Logger LOGGER = LoggerFactory.getLogger(JavaProgramElement.class);

    private static final Comment[] NO_COMMENTS = new Comment[0];

    private final Comment[] comments;

    private int hashCode = -1;

    public JavaProgramElement() {
        comments = NO_COMMENTS;
    }


    /**
     * Java program element.
     *
     * @param list ExtList with comments
     */
    public JavaProgramElement(ExtList list) {
        super(list);
        comments = extractComments(list);
    }


    /**
     * creates a java program element with the given position information
     *
     * @param pos the PositionInfo where the Java program element occurs in the source
     */
    public JavaProgramElement(PositionInfo pos) {
        super(pos);
        comments = NO_COMMENTS;
    }


    public JavaProgramElement(ExtList children, PositionInfo pos) {
        super(children, pos);
        comments = extractComments(children);
    }


    /**
     * collects comments contained in the given list
     *
     * @param list the ExtList with children and comments of this node
     */
    private Comment[] extractComments(ExtList list) {
        final Comment[] c = list.collect(Comment.class);
        return c == null ? NO_COMMENTS : c;
    }


    /**
     * Get comments.
     *
     * @return the comments.
     */
    @Override
    public Comment[] getComments() {
        return comments;
    }



    @Override
    public void prettyPrint(PrettyPrinter w) throws IOException {
        int s = (comments != null) ? comments.length : 0;
        int t = 0;
        for (int i = 0; i < s; i += 1) {
            Comment c = comments[i];
            if (c.isPrefixed()) {
                c.prettyPrint(w);
            } else {
                t += 1;
            }
        }
        prettyPrintMain(w);
        if (t > 0) {
            for (int i = 0; i < s; i += 1) {
                Comment c = comments[i];
                if (!c.isPrefixed()) {
                    if (c instanceof SingleLineComment) {
                        w.scheduleComment((SingleLineComment) c);
                    } else {
                        c.prettyPrint(w);
                    }
                }
            }
        }
    }


    /**
     * Prints main content of current node and all syntactical children. Hook method of prettyPrint;
     * defaults to do nothing.
     */
    protected void prettyPrintMain(PrettyPrinter w) throws IOException {}



    /**
     * commented in interface SourceElement. The default equals method compares two elements by
     * testing if they have the same type and calling the default equals method.
     */
    @Override
    public boolean equalsModRenaming(SourceElement se, NameAbstractionTable nat) {
        return (this.getClass() == se.getClass());
    }

    protected int computeHashCode() {
        int result = 17 * this.getClass().hashCode();
        return result;
    }

    /**
     * if you need to customize the hashcode computation for a subclass please override method
     * {@link #computeHashCode()}
     */
    @Override
    public final int hashCode() {
        if (hashCode == -1) {
            int localHash = computeHashCode();
            if (localHash == -1) {
                localHash = 1;
            }
            this.hashCode = localHash;
        }
        return hashCode;
    }

    @Override
    public boolean equals(Object o) {
        if (o == this) {
            return true;
        }
        if (o == null || o.getClass() != this.getClass()) {
            return false;
        }

        return equalsModRenaming((JavaProgramElement) o, NameAbstractionTableDisabled.INSTANCE);
    }


    /**
     * this is the default implementation of the signature, which is used to determine program
     * similarity.
     *
     * @param ec TODO
     */
    public String reuseSignature(Services services, ExecutionContext ec) {
        final String s = getClass().toString();
        return s.substring(s.lastIndexOf('.') + 1, s.length());
    }


    /**
     * this class is used by method call. As in this case we do not want to abstract from names
     */
    static class NameAbstractionTableDisabled extends NameAbstractionTable {


        public static final NameAbstractionTableDisabled INSTANCE =
            new NameAbstractionTableDisabled();

        public void add(SourceElement pe1, SourceElement pe2) {}

        public boolean sameAbstractName(SourceElement pe1, SourceElement pe2) {
            return pe1.equals(pe2);
        }
    }


    @Override
    public MatchConditions match(SourceData source, MatchConditions matchCond) {
        final ProgramElement src = source.getSource();
        LOGGER.debug("Program match start (template {}, source {})", this, src);

        if (src.getClass() != getClass()) {
            LOGGER.debug("Program match failed. Incompatible AST nodes (template {}, source {})",
                this, src);
            LOGGER.debug("Incompatible AST nodes (template {}, source {})", this.getClass(),
                src.getClass());
            return null;
        }
        source.next();
        return matchCond;
    }
}
