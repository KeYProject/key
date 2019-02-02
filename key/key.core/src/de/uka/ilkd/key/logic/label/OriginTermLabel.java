package de.uka.ilkd.key.logic.label;

import java.nio.file.Paths;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
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
 * for every term you have added to the original contract in your PO to add an
 * {@link OriginTermLabel}
 * of your choosing. Terms for which you do not do this get a label of the form
 * {@code new OriginTermLabel(SpecType.NONE, null, -1)}. </p>
 *
 * @author lanzinger
 */
public class OriginTermLabel implements TermLabel {

    /**
     * Display name for {@link OriginTermLabel}s.
     */
    public final static Name NAME = new Name("origin");

    /**
     * @see #getChildCount()
     */
    public final static int CHILD_COUNT = 2;

    /**
     * The term's origin.
     * @see #getOrigin()
     */
    private Origin origin;

    /**
     * The origins of the term's sub-terms and former sub-terms.
     * @see #getSubtermOrigins()
     */
    private Set<Origin> subtermOrigins;

    /**
     * Creates a new {@link OriginTermLabel}.
     *
     * @param origin the term's origin.
     */
    public OriginTermLabel(Origin origin) {
        this.origin = origin;
        this.subtermOrigins = new HashSet<>();
    }

    /**
     * Creates a new {@link OriginTermLabel}.
     *
     * @param origin the term's origin.
     * @param subtermOrigins the origins of the term's (former) subterms.
     */
    public OriginTermLabel(Origin origin, Set<Origin> subtermOrigins) {
        this(origin);
        this.subtermOrigins.addAll(subtermOrigins);
        this.subtermOrigins = this.subtermOrigins.stream()
                .filter(o -> o.specType != SpecType.NONE).collect(Collectors.toSet());
    }

    /**
     * Creates a new {@link OriginTermLabel}.
     *
     * @param specType the JML spec type the term originates from.
     * @param file the file the term originates from.
     * @param line the line in the file.
     * @param subtermOrigins the origins of the term's (former) subterms.
     */
    public OriginTermLabel(SpecType specType, String file, int line, Set<Origin> subtermOrigins) {
        this(specType, file, line);
        this.subtermOrigins.addAll(subtermOrigins);
        this.subtermOrigins = this.subtermOrigins.stream()
                .filter(o -> o.specType != SpecType.NONE).collect(Collectors.toSet());
    }

    /**
     * Creates a new {@link OriginTermLabel}.
     *
     * @param specType the JML spec type the term originates from.
     * @param file the file the term originates from.
     * @param line the line in the file.
     */
    public OriginTermLabel(SpecType specType, String file, int line) {
        String filename = file == null || file.equals("no file")
                ? null
                        : Paths.get(file).getFileName().toString();

        this.origin = new Origin(specType, filename, line);
        this.subtermOrigins = new HashSet<>();
    }

    /**
     * Creates a new {@link OriginTermLabel}.
     *
     * @param subtermOrigins the origins of the term's (former) subterms.
     */
    public OriginTermLabel(Set<Origin> subtermOrigins) {
        this.origin = new Origin(SpecType.NONE, null, -1);
        this.subtermOrigins = new HashSet<>();
        this.subtermOrigins.addAll(subtermOrigins);
        this.subtermOrigins = this.subtermOrigins.stream()
                .filter(o -> o.specType != SpecType.NONE).collect(Collectors.toSet());
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((origin == null) ? 0 : origin.hashCode());
        result = prime * result + ((subtermOrigins == null) ? 0 : subtermOrigins.hashCode());
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj instanceof OriginTermLabel) {
            OriginTermLabel other = (OriginTermLabel) obj;
            return other.origin.equals(origin) && other.subtermOrigins.equals(subtermOrigins);
        } else {
            return false;
        }
    }

    /**
     * <p> Determines whether an {@code OriginTermLabel} can be added to the specified term. </p>
     *
     * <p> E.g., no labels should be added to terms whose operator is a heap variable as this leads
     * to various problems during proof search. </p>
     *
     * @param term a term
     * @param services services.
     * @return {@code true} iff an {@code OriginTermLabel} can be added to the specified term.
     */
    public static boolean canAddLabel(Term term, Services services) {
        return canAddLabel(term.op(), services);
    }

    /**
     * <p> Determines whether an {@code OriginTermLabel} can be added to a term with the specified
     * operator. </p>
     *
     * <p> E.g., no labels should be added to terms whose operator is a heap variable as this leads
     * to various problems during proof search. </p>
     *
     * @param op the specified operator.
     * @param services the services object.
     * @return {@code true} iff an {@code OriginTermLabel} can be added to a term
     *  with the specified operator.
     */
    public static boolean canAddLabel(Operator op, Services services) {
        if (op.arity() == 0) {
            Sort sort = op.sort(new ImmutableArray<>());
            Sort heapSort = services.getTypeConverter().getHeapLDT().getHeap().sort();

            return sort.extendsTrans(Sort.FORMULA)
                    || (op instanceof ProgramVariable && !sort.equals(heapSort));
        } else {
            return true;
        }
    }

    /**
     * Removes all {@link OriginTermLabel} from the specified term and its sub-terms.
     *
     * @param term the term to transform.
     * @param services services.
     * @return the transformed term.
     */
    public static Term removeOriginLabels(Term term, Services services) {
        List<TermLabel> labels = term.getLabels().toList();
        TermLabel originTermLabel = term.getLabel(NAME);
        TermBuilder tb = services.getTermBuilder();
        ImmutableArray<Term> oldSubs = term.subs();
        Term[] newSubs = new Term[oldSubs.size()];

        if (originTermLabel != null) {
            labels.remove(originTermLabel);
        }

        for (int i = 0; i < newSubs.length; ++i) {
            newSubs[i] = removeOriginLabels(oldSubs.get(i), services);
        }

        return tb.tf().createTerm(
                term.op(),
                newSubs,
                term.boundVars(),
                term.javaBlock(),
                new ImmutableArray<>(labels));
    }

    /**
     * This method transforms a term in such a way that
     * every {@link OriginTermLabel} contains all of the correct
     * {@link #getSubtermOrigins()}.
     *
     * @param term the term to transform.
     * @param services services.
     * @return the transformed term.
     */
    public static Term collectSubtermOrigins(Term term, Services services) {
        if (!canAddLabel(term, services)) {
            return term;
        }

        final boolean addOriginLabels = services.getProof() != null
                && services.getProof().getSettings().getTermLabelSettings().getUseOriginLabels();

        TermBuilder tb = services.getTermBuilder();
        ImmutableArray<Term> oldSubs = term.subs();
        Term[] newSubs = new Term[oldSubs.size()];
        Set<Origin> origins = new HashSet<>();

        for (int i = 0; i < newSubs.length; ++i) {
            newSubs[i] = collectSubtermOrigins(oldSubs.get(i), services);
            OriginTermLabel subLabel = (OriginTermLabel) newSubs[i].getLabel(NAME);

            if (subLabel != null) {
                origins.add(subLabel.getOrigin());
                origins.addAll(subLabel.getSubtermOrigins());
            }
        }

        List<TermLabel> labels = term.getLabels().toList();
        OriginTermLabel oldLabel = (OriginTermLabel) term.getLabel(NAME);

        if (oldLabel != null) {
            labels.remove(oldLabel);

            if ((!origins.isEmpty() || oldLabel.getOrigin().specType != SpecType.NONE)
                    && addOriginLabels) {
                labels.add(new OriginTermLabel(
                        oldLabel.getOrigin().specType,
                        oldLabel.getOrigin().fileName,
                        oldLabel.getOrigin().line,
                        origins));
            }
        } else if (!origins.isEmpty() && addOriginLabels) {
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
        return CHILD_COUNT;
    }

    @Override
    public boolean isStrategyRelevant() {
        return false;
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

    /**
     * An origin encapsulates some information about where in the JML specification a term
     * originates from.
     *
     * @author lanzinger
     */
    public static class Origin implements Comparable<Origin> {

        /**
         * The JML spec type the term originates from.
         */
        public final SpecType specType;

        /**
         * The file the term originates from.
         */
        public final String fileName;

        /**
         * The line in the file the term originates from.
         */
        public final int line;

        /**
         * Creates a new {@link OriginTermLabel.Origin}.
         *
         * @param specType the JML spec type the term originates from.
         * @param fileName the file the term originates from.
         * @param line the line in the file.
         */
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
                sb.append(" @ line ");
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
            if (this == obj) {
                return true;
            }

            if (obj == null) {
                return false;
            }

            if (getClass() != obj.getClass()) {
                return false;
            }

            Origin other = (Origin) obj;

            if (fileName == null) {
                if (other.fileName != null) {
                    return false;
                }
            } else if (!fileName.equals(other.fileName)) {
                return false;
            }

            if (line != other.line) {
                return false;
            }

            if (specType != other.specType) {
                return false;
            }

            return true;
        }
    }

    /**
     * A {@code SpecType} is any type of JML specification which gets translated into JavaDL.
     *
     * @author lanzinger
     * @see OriginTermLabel.Origin
     */
    public static enum SpecType {

        /**
         * accessible
         */
        ACCESSIBLE("accessible"),

        /**
         * assignable
         */
        ASSIGNABLE("assignable"),

        /**
         * decreases
         */
        DECREASES("decreases"),

        /**
         * measured_by
         */
        MEASURED_BY("measured_by"),

        /**
         * invariant
         */
        INVARIANT("invariant"),

        /**
         * loop_invariant
         */
        LOOP_INVARIANT("loop_invariant"),

        /**
         * loop_invariant_free
         */
        LOOP_INVARIANT_FREE("loop_invariant_free"),

        /**
         * requires
         */
        REQUIRES("requires"),

        /**
         * requires_free
         */
        REQUIRES_FREE("requires_free"),

        /**
         * ensures
         */
        ENSURES("ensures"),

        /**
         * ensures_free
         */
        ENSURES_FREE("ensures_free"),

        /**
         * signals
         */
        SIGNALS("signals"),

        /**
         * signals_only
         */
        SIGNALS_ONLY("signals_only"),

        /**
         * breaks
         */
        BREAKS("breaks"),

        /**
         * continues
         */
        CONTINUES("continues"),

        /**
         * returns
         */
        RETURNS("returns"),

        /**
         * None. Used for terms that do not originate from a JML spec and terms whose origin was
         * not set upon their creation.
         */
        NONE("<none>");

        /**
         * This {@code SpecType}'s string representation.
         */
        private String name;

        /**
         * Creates a new {@code SpecType}
         *
         * @param name the {@code SpecType}'s string representation.
         */
        private SpecType(String name) {
            this.name = name;
        }

        @Override
        public String toString() {
            return name;
        }
    }
}
