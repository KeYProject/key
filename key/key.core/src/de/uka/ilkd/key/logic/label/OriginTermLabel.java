package de.uka.ilkd.key.logic.label;

import java.nio.file.Paths;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.rule.label.OriginTermLabelRefactoring;

/**
 * <p> An {@link OriginTermLabel} saves a term's origin in the JML specification
 * ({@link #getOrigin()}) as well as the origins of all of its subterms and former
 * subterms ({@link #getSubtermOrigins()}). </p>
 *
 * <p> For this to work correctly, you must call
 * {@link #collectSubtermOrigins(Term, TermBuilder)} for every top-level formula in your
 * original proof obligation. </p>
 *
 * <p> Before doing this, you can call {@link TermBuilder#addLabelToAllSubs(Term, TermLabel)}
 * for every term you have added to the original contract in your PO to add an {@link OriginTermLabel}
 * of your choosing. Terms for which you do not do this get a label of the form
 * {@code new OriginTermLabel(SpecType.NONE, null, -1)}. </p>
 *
 * @author lanzinger
 */
public class OriginTermLabel implements TermLabel {

    public final static Name NAME = new Name("Origin");

    private Origin origin;
    private Set<Origin> subtermOrigins;

    /**
     * This method transforms a term in such a way that
     *
     * <ol>
     *  <li> every sub-term of has a {@link OriginTermLabel}
     *      (sub-terms that did not have one previously get a label with
     *      SpecType {@link SpecType#NONE}). </li>
     *  <li> every {@link OriginTermLabel} contains all of the correct
     *      {@link #getSubtermOrigins()}. </li>
     * </ol>
     *
     * @param term the term to transform.
     * @param tb the term builder to use for the transformation.
     * @return the transformed term.
     */
    public static Term collectSubtermOrigins(Term term, TermBuilder tb) {
        ImmutableArray<Term> oldSubs = term.subs();
        Term[] newSubs = new Term[oldSubs.size()];
        Set<Origin> origins = new HashSet<>();

        for (int i = 0; i < newSubs.length; ++i) {
            newSubs[i] = collectSubtermOrigins(oldSubs.get(i), tb);
            OriginTermLabel subLabel = (OriginTermLabel) newSubs[i].getLabel(NAME);
            origins.add(subLabel.getOrigin());
            origins.addAll(subLabel.getSubtermOrigins());
        }

        List<TermLabel> labels = term.getLabels().toList();
        OriginTermLabel oldLabel = (OriginTermLabel) term.getLabel(NAME);

        if (oldLabel != null) {
            labels.remove(oldLabel);
            labels.add(new OriginTermLabel(
                    oldLabel.getOrigin().specType,
                    oldLabel.getOrigin().fileName,
                    oldLabel.getOrigin().line,
                    origins));
        } else {
            labels.add(new OriginTermLabel(
                    SpecType.NONE,
                    null,
                    -1,
                    origins));
        }

        return tb.tf().createTerm(
                term.op(),
                newSubs,
                term.boundVars(),
                term.javaBlock(),
                new ImmutableArray<>(labels));
    }

    public OriginTermLabel(SpecType specType, String file, int line, Set<Origin> subtermOrigins) {
        this(specType, file, line);
        this.subtermOrigins.addAll(subtermOrigins);
        this.subtermOrigins = this.subtermOrigins.stream()
                .filter(o -> o.specType != SpecType.NONE).collect(Collectors.toSet());
    }

    public OriginTermLabel(SpecType specType, String file, int line) {
        String filename = file == null || file.equals("no file")
                ? null
                : Paths.get(file).getFileName().toString();

        this.origin = new Origin(specType, filename, line);
        this.subtermOrigins = new HashSet<>();
    }

    public OriginTermLabel(Set<Origin> subtermOrigins) {
        this.origin = new Origin(SpecType.NONE, null, -1);
        this.subtermOrigins = new HashSet<>();
        this.subtermOrigins.addAll(subtermOrigins);
        this.subtermOrigins = this.subtermOrigins.stream()
                .filter(o -> o.specType != SpecType.NONE).collect(Collectors.toSet());
    }

    @Override
    public String toString() {
        return "" + NAME + "(" + origin + ") (" + subtermOrigins + ")";
    }

    @Override
    public Name name() {
        return NAME;
    }

    @Override
    public Object getChild(int i) {
        if (i == 0) {
            return origin;
        } else if (i == 1) {
            return subtermOrigins;
        } else {
            return null;
        }
    }

    @Override
    public int getChildCount() {
        return 1;
    }

    /**
     *
     * @return the term's origin.
     */
    public Origin getOrigin() {
        return origin;
    }

    /**
     * <p> Returns the origins of the term's sub-terms and former sub-terms. </p>
     *
     * <p> Note that you need to have called {@link #collectSubtermOrigins(Term, TermBuilder)}
     * for this method to work correctly. </p>
     *
     * @return the origins of the term's sub-terms and former sub-terms.
     * @see OriginTermLabelRefactoring
     */
    public Set<Origin> getSubtermOrigins() {
        return Collections.unmodifiableSet(subtermOrigins);
    }

    public static class Origin implements Comparable<Origin> {

        public final SpecType specType;
        public final String fileName;
        public final int line;

        public Origin(SpecType specType, String fileName, int line) {
            this.specType = specType;
            this.fileName = fileName;
            this.line = line;
        }

        @Override
        public String toString() {
            StringBuilder sb = new StringBuilder(specType.toString());

            if (fileName != null) {
                sb.append(" @ ");
                sb.append(fileName);
                sb.append(", line ");
                sb.append(line);
            } else if (specType != SpecType.NONE) {
                sb.append(" (implicit)");
            }

            return sb.toString();
        }

        @Override
        public int compareTo(Origin other) {
            int result = specType.toString().compareTo(other.specType.toString());

            if (result == 0) {
                result = fileName.compareTo(other.fileName);

                if (result == 0) {
                    result = Integer.compare(line, other.line);
                }
            }

            return result;
        }

        @Override
        public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result + ((fileName == null) ? 0 : fileName.hashCode());
            result = prime * result + line;
            result = prime * result + ((specType == null) ? 0 : specType.hashCode());
            return result;
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj)
                return true;
            if (obj == null)
                return false;
            if (getClass() != obj.getClass())
                return false;
            Origin other = (Origin) obj;
            if (fileName == null) {
                if (other.fileName != null)
                    return false;
            } else if (!fileName.equals(other.fileName))
                return false;
            if (line != other.line)
                return false;
            if (specType != other.specType)
                return false;
            return true;
        }
    }

    public static enum SpecType {

        ACCESSIBLE("accessible"),
        ASSIGNABLE("assignable"),
        DECREASES("decreases"),
        MEASURED_BY("measured_by"),
        CLASS_INVARIANT("invariant"),
        LOOP_INVARIANT("loop_invariant"),
        LOOP_INVARIANT_FREE("loop_invariant_free"),
        REQUIRES("requires"),
        REQUIRES_FREE("requires_free"),
        ENSURES("ensures"),
        ENSURES_FREE("ensures_free"),
        SIGNALS("signals"),
        SIGNALS_ONLY("signals_only"),
        BREAKS("breaks"),
        CONTINUES("continues"),
        RETURNS("returns"),
        NONE("<none>");

        private String name;

        private SpecType(String name) {
            this.name = name;
        }

        @Override
        public String toString() {
            return name;
        }
    }
}
