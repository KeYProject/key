/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.pp;


import java.util.ArrayDeque;

import de.uka.ilkd.key.util.pp.Layouter;
import de.uka.ilkd.key.util.pp.StringBackend;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class PosTableLayouter extends Layouter<PosTableLayouter.Mark> {
    private static final Logger LOGGER = LoggerFactory.getLogger(PosTableLayouter.class);

    /**
     * The default and minimal value of the max. number of characters to put in one line
     */
    public static final int DEFAULT_LINE_WIDTH = 55;

    /**
     * Line indent in spaces
     */
    public static final int INDENT = 2;

    /**
     * If pure is true the PositionTable will not be calculated
     */
    private final boolean pure;

    /**
     * Creates a new layouter.
     *
     * @param lineWidth the line width to use
     * @param indentation the default indentation to use
     * @param pure if true a position table will be generated
     */
    public PosTableLayouter(int lineWidth, int indentation, boolean pure) {
        super(pure ? new StringBackend<>() : new PosTableStringBackend(), lineWidth, indentation);
        this.pure = pure;
    }

    /**
     * Creates a new layouter that will not generate a position table.
     *
     * @param lineWidth the line width to use
     */
    public static PosTableLayouter pure(int lineWidth) {
        return new PosTableLayouter(lineWidth, INDENT, true);
    }

    /**
     * Creates a new layouter that will not generate a position table.
     */
    public static PosTableLayouter pure() {
        return pure(DEFAULT_LINE_WIDTH);
    }

    /**
     * Creates a new layouter that will generate a position table.
     *
     * @param lineWidth the line width to use
     */
    public static PosTableLayouter positionTable(int lineWidth) {
        return new PosTableLayouter(lineWidth, INDENT, false);
    }

    /**
     * Creates a new layouter that will generate a position table.
     */
    public static PosTableLayouter positionTable() {
        return positionTable(DEFAULT_LINE_WIDTH);
    }

    /**
     * @return true if a position table will be generated
     */
    public boolean isPure() {
        return pure;
    }

    /**
     * Creates a new layouter with the same settings
     */
    public PosTableLayouter cloneArgs() {
        int lineWidth = lineWidth();
        int indent = defaultIndent();
        return new PosTableLayouter(lineWidth, indent, pure);
    }

    public void mark(MarkType type, int parameter) {
        if (!pure) {
            mark(new Mark(type, parameter));
        }
    }

    protected void mark(MarkType type) {
        mark(type, -1);
    }

    public void markModPosTbl() {
        mark(MarkType.MARK_MOD_POS_TBL);
    }

    public void markStartFirstStatement() {
        mark(MarkType.MARK_START_FIRST_STMT);
    }

    public void markEndFirstStatement() {
        mark(MarkType.MARK_END_FIRST_STMT);
    }

    public void markStartUpdate() {
        mark(MarkType.MARK_START_UPDATE);
    }

    public void markEndUpdate() {
        mark(MarkType.MARK_END_UPDATE);
    }

    /**
     * Called before a substring is printed that has its own entry in a position table. The method
     * sends a mark to the layouter, which will make the backend set a start entry in posTbl, push a
     * new StackEntry with the current posTbl and current pos on the stack and set the current pos
     * to the length of the current string result. Subclasses may overwrite this method with an
     * empty body if position information is not needed there.
     */
    public void markStartSub() {
        mark(MarkType.MARK_START_SUB);
    }

    /**
     * TODO
     */
    public void markStartSub(int subterm) {
        mark(MarkType.MARK_START_SUB, subterm);
    }

    /**
     * Called after a substring is printed that has its own entry in a position table. The backend
     * will finish the position table on the top of the stack and set the entry on the top of the
     * stack to be the current position/position table. Subclasses may overwrite this method with an
     * empty body if position information is not needed there.
     */
    public void markEndSub() {
        mark(MarkType.MARK_END_SUB);
    }

    /**
     * Called before keyword is printed and marks current position.
     */
    public void markStartKeyword() {
        mark(MarkType.MARK_START_KEYWORD);
    }

    /**
     * Called before java block is printed and marks current position.
     */
    public void markStartJavaBlock() {
        mark(MarkType.MARK_START_JAVA_BLOCK);
    }

    /**
     * Called after java block is printed and marks current position.
     */
    public void markEndJavaBlock() {
        mark(MarkType.MARK_END_JAVA_BLOCK);
    }

    /**
     * Called after keyword is printed and marks current position.
     */
    public void markEndKeyword() {
        mark(MarkType.MARK_END_KEYWORD);
    }

    /**
     * Start a term with subterms. The backend will set the current posTbl to a newly created
     * position table with the given number of rows. Subclasses may overwrite this method with an
     * empty body if position information is not needed there.
     *
     * @param size the number of rows of the new position table
     */
    public void startTerm(int size) {
        mark(MarkType.MARK_START_TERM, size);
    }

    public PosTableLayouter keyWord(String kw) {
        markStartKeyword();
        print(kw);
        markEndKeyword();
        return this;
    }

    /**
     * returns the PositionTable representing position information on the sequent of this
     * LogicPrinter. Subclasses may overwrite this method with a null returning body if position
     * information is not computed there.
     */
    public InitialPositionTable getInitialPositionTable() {
        if (pure) {
            return null;
        }
        return ((PosTableStringBackend) backend()).getInitialPositionTable();
    }

    public enum MarkType {
        /**
         * Mark the beginning of a term
         */
        MARK_START_TERM,
        /**
         * Mark the start of a subterm. Needed for PositionTable construction.
         */
        MARK_START_SUB,
        /**
         * Mark the end of a subterm. Needed for PositionTable construction.
         */
        MARK_END_SUB,
        /**
         * Mark the start of the first executable statement. Needed for PositionTable construction.
         */
        MARK_START_FIRST_STMT,
        /**
         * Mark the end of the first executable statement. Needed for PositionTable construction.
         */
        MARK_END_FIRST_STMT,
        /**
         * Mark the need for a ModalityPositionTable. The next startTerm mark will construct a
         * ModalityPositionTable instead of the usual PositionTable. Needed for PositionTable
         * construction.
         */
        MARK_MOD_POS_TBL,
        /**
         * Mark the start of an update.
         */
        MARK_START_UPDATE,
        /**
         * Mark the end of an update.
         */
        MARK_END_UPDATE,
        /**
         * Mark the beginning of a keyword.
         */
        MARK_START_KEYWORD,
        /**
         * Mark the end of a keyword.
         */
        MARK_END_KEYWORD,
        /**
         * Mark the beginning of a java block.
         */
        MARK_START_JAVA_BLOCK,
        /**
         * Mark the end of a java block.
         */
        MARK_END_JAVA_BLOCK,
    }

    public static final class Mark {
        public final MarkType type;
        public final int parameter;

        public Mark(MarkType type, int parameter) {
            this.type = type;
            this.parameter = parameter;
        }
    }

    /**
     * Utility class for stack entries containing the position table and the position of the start
     * of the subterm in the result.
     */
    private static class StackEntry {
        final PositionTable posTbl;
        final int p;

        StackEntry(PositionTable posTbl, int p) {
            this.posTbl = posTbl;
            this.p = p;
        }

        PositionTable posTbl() {
            return posTbl;
        }

        int pos() {
            return p;
        }
    }

    /**
     * A {@link de.uka.ilkd.key.util.pp.Backend} which puts its result in a StringBuffer and builds
     * a PositionTable. Position table construction is done using the
     * {@link de.uka.ilkd.key.util.pp.Layouter#mark(Object)} facility of the layouter with the
     * various static <code>MARK_</code> objects.
     */
    private static class PosTableStringBackend extends StringBackend<Mark> {

        /**
         * The top PositionTable
         */
        private final InitialPositionTable initPosTbl = new InitialPositionTable();

        /**
         * The resulting position table or an intermediate result
         */
        private PositionTable posTbl = initPosTbl;

        /**
         * The position in result where the current subterm starts
         */
        private int pos = 0;

        /**
         * The stack of StackEntry representing the nodes above the current subterm
         */
        private final ArrayDeque<StackEntry> stack = new ArrayDeque<>();

        /**
         * If this is set, a ModalityPositionTable will be built next.
         */
        private boolean need_modPosTable = false;

        /**
         * These two remember the range corresponding to the first executable statement in a
         * JavaBlock
         */
        private int firstStmtStart;

        /**
         * Remembers the start of an update to create a range
         */
        private final ArrayDeque<Integer> updateStarts = new ArrayDeque<>();

        /**
         * Remembers the start of a keyword to create a range.
         */
        private final ArrayDeque<Integer> keywordStarts = new ArrayDeque<>();

        /**
         * Remembers the start of a java block to create a range.
         */
        private final ArrayDeque<Integer> javaBlockStarts = new ArrayDeque<>();

        PosTableStringBackend() {}

        /**
         * Returns the constructed position table.
         *
         * @return the constructed position table
         */
        public InitialPositionTable getInitialPositionTable() {
            return initPosTbl;
        }

        /**
         * Receive a mark and act appropriately.
         */
        @Override
        public void mark(Mark pair) {
            MarkType markType = pair.type;
            int parameter = pair.parameter;

            // IMPLEMENTATION NOTE
            //
            // This if-cascade is hideous. In particular the part
            // which says <code>instanceof Integer</code>, which stand
            // for a startTerm with given arity.
            //
            // The alternative would be to 1.: spread these
            // mini-functionalities across several inner classes in a
            // visitor-like style, effectively preventing anybody from
            // finding out what happens, and 2.: allocate separate
            // objects for each startTerm call to wrap the arity.
            //
            // I (MG) prefer it this way.
            //
            // MU refactored this using enums which makes it a little less ugly
            // and more flexible.
            switch (markType) {
            case MARK_START_SUB:
                if (parameter == -1) {
                    // no parameter means subterms in normal order
                    posTbl.setStart(count() - pos);
                } else {
                    // parameter means a particular subterm has been chosen
                    posTbl.setStart(parameter, count() - pos);
                }
                stack.push(new StackEntry(posTbl, pos));
                pos = count();
                break;

            case MARK_END_SUB:
                StackEntry se = stack.peek();
                stack.pop();
                pos = se.pos();
                se.posTbl().setEnd(count() - pos, posTbl);
                posTbl = se.posTbl();
                break;

            case MARK_MOD_POS_TBL:
                need_modPosTable = true;
                break;

            case MARK_START_TERM:
                // This is sent by startTerm
                if (need_modPosTable) {
                    posTbl = new ModalityPositionTable(parameter);
                } else {
                    posTbl = new PositionTable(parameter);
                }
                need_modPosTable = false;
                break;

            case MARK_START_FIRST_STMT:
                firstStmtStart = count() - pos;
                break;

            case MARK_END_FIRST_STMT:
                if (posTbl instanceof ModalityPositionTable) {
                    Range firstStmtRange = new Range(firstStmtStart, count() - pos);
                    ((ModalityPositionTable) posTbl).setFirstStatementRange(firstStmtRange);
                }
                break;

            case MARK_START_UPDATE:
                updateStarts.push(count());
                break;

            case MARK_END_UPDATE:
                int updateStart = updateStarts.pop();
                initPosTbl.addUpdateRange(new Range(updateStart, count()));
                break;
            case MARK_START_KEYWORD:
                keywordStarts.push(count());
                break;
            case MARK_END_KEYWORD:
                initPosTbl.addKeywordRange(new Range(keywordStarts.pop(), count()));
                break;
            case MARK_START_JAVA_BLOCK:
                javaBlockStarts.push(count());
                break;
            case MARK_END_JAVA_BLOCK:
                initPosTbl.addJavaBlockRange(new Range(javaBlockStarts.pop(), count()));
                break;

            default:
                LOGGER.error("Unexpected mark: {}", markType);
            }
        }
    }
}
