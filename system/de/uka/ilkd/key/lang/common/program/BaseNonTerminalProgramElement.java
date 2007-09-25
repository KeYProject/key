package de.uka.ilkd.key.lang.common.program;

import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.NonTerminalProgramElement;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.SourceData;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ExtList;

/**
 * Base implementation of non-terminal program elements.
 * 
 * @author oleg.myrk@gmail.com
 */
public abstract class BaseNonTerminalProgramElement extends BaseProgramElement
                implements INonTerminalProgramElement {

        /**
         * Precomputed value of the hash code.
         */
        private Integer hashCode;

        public BaseNonTerminalProgramElement() {
                super();
        }

        public BaseNonTerminalProgramElement(ExtList children) {
                super(children);
        }

        public BaseNonTerminalProgramElement(ExtList children,
                        BaseNonTerminalProgramElement original) {
                super(children, original);
        }

        /**
         * @inheritDocs
         */
        public final ProgramElement getChildAt(int index) {
                return getProgramElementAt(index);
        }

        /**
         * Reduces the equality to the equality of runtime classes and the
         * equality of children.
         */
        public boolean equalsModRenaming(IProgramElement pe,
                        NameAbstractionTable nat) {
                if (this.getClass() != pe.getClass()) {
                        return false;
                }
                final INonTerminalProgramElement nte = (INonTerminalProgramElement) pe;

                if (nte.getChildCount() != getChildCount()) {
                        return false;
                }

                for (int i = 0, cc = getChildCount(); i < cc; i++) {
                        if (!getChildAt(i).equalsModRenaming(nte.getChildAt(i),
                                        nat)) {
                                return false;
                        }
                }
                return true;
        }

        /**
         * Computes hashcode in terms of children. Is called only once and then
         * cached. Can be overridden in subclasses.
         */
        protected int computeHashCode() {
                int result = 17;
                result = 37 * result + getChildCount();
                for (int i = 0, cc = getChildCount(); i < cc; i++) {
                        result = 37 * result + getChildAt(i).hashCode();
                }
                return result;
        }

        /**
         * @inheritDocs
         */
        public int hashCode() {
                if (hashCode == null)
                        hashCode = Integer.valueOf(computeHashCode());
                return hashCode.intValue();
        }

        /**
         * Reduces matching to equality of runtime classes and the matching of
         * children.
         */
        public MatchConditions match(SourceData source,
                        MatchConditions matchCond) {
                final ProgramElement src = source.getSource();

                Debug.out("Program match start (template, source)", this, src);

                if (src == null) {
                        return null;
                }

                if (src.getClass() != this.getClass()) {
                        Debug.out("Incompatible AST nodes (template, source)",
                                        this, src);
                        return null;
                }

                final NonTerminalProgramElement ntSrc = (NonTerminalProgramElement) src;
                final SourceData newSource = new SourceData(ntSrc, 0, source
                                .getServices());

                matchCond = matchChildren(newSource, matchCond, 0);

                if (matchCond == null) {
                        return null;
                }

                source.next();
                return matchCond;
        }

        /**
         * Matches successively all children of this current node. Thereby the
         * <tt>offset</tt>-th child is matched against
         * <code>source.getSource()</code>. The call <tt>source.next</tt>
         * has to be done in the
         * 
         * @link ProgramElement#match method of the currently matched child in
         *       case of a successful match. This is <em>not</em> done here
         *       (rationale: schemavariables matching on lists can be
         *       implemented easy).
         * 
         * 
         * @param source
         *                the SourceData with the children to be matched
         * @param matchCond
         *                the MatchConditions found so far
         * @param offset
         *                the int denoting the index of the child to start with
         * @return the resulting match conditions or <tt>null</tt> if matching
         *         failed
         */
        protected MatchConditions matchChildren(SourceData source,
                        MatchConditions matchCond, int offset) {

                for (int i = offset, sz = getChildCount(); i < sz; i++) {
                        matchCond = getChildAt(i).match(source, matchCond);
                        if (matchCond == null) {
                                return null;
                        }
                }

                if (source.getSource() != null) {
                        Debug.out("Source has unmatched elements.");
                        return null;
                }

                return matchCond;
        }

}
