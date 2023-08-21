/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.pp.PrettyPrinter;

import org.key_project.util.EqualsModProofIrrelevancy;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public final class JavaBlock implements EqualsModProofIrrelevancy {
    private static final Logger LOGGER = LoggerFactory.getLogger(JavaBlock.class);

    /**
     * Attention using the JavaBlock below means no program not the empty program. It is used as a
     * realization of the sentinel design pattern to mark terms with operators that are incapable of
     * containing a program like predicate symbols.
     *
     * If you want to have an empty program, create a new JavaBlock instance with an empty statement
     * block.
     *
     */
    public static final JavaBlock EMPTY_JAVABLOCK = new JavaBlock(new StatementBlock());

    private final JavaProgramElement prg;
    private int hashCode = -1;


    /**
     * create a new JavaBlock
     *
     * @param prg the root JavaProgramElement for this JavaBlock
     */
    private JavaBlock(JavaProgramElement prg) {
        this.prg = prg;
    }

    /**
     * create a new JavaBlock
     *
     * @param prg the root StatementBlock for this JavaBlock. TacletIndex relies on <code>prg</code>
     *        being indeed a StatementBlock.
     */
    public static JavaBlock createJavaBlock(StatementBlock prg) {
        assert prg != null;
        /*
         * if (prg.isEmpty() && ! ) { return EMPTY_JAVABLOCK; }
         */
        return new JavaBlock(prg);
    }


    public boolean isEmpty() {
        if ((program() instanceof StatementBlock)) {
            return ((StatementBlock) program()).isEmpty();
        }
        return this == EMPTY_JAVABLOCK;
    }

    public int size() {
        if ((program() instanceof StatementBlock)) {
            return ((StatementBlock) program()).getChildCount();
        }
        return 0;
    }

    /** returns the hashCode */
    public int hashCode() {
        return 17 + ((program() == null) ? 0 : program().hashCode());
    }

    /** returns true iff the program elements are equal */
    public boolean equals(Object o) {
        if (o == this) {
            return true;
        } else if (!(o instanceof JavaBlock)) {
            return false;
        } else {
            JavaBlock block = (JavaBlock) o;

            if (block.program() == null) {
                return program() == null;
            } else {
                return block.program().equals(program());
            }
        }
    }

    /**
     * returns true if the given ProgramElement is equal to the one of the JavaBlock modulo renaming
     * (see comment in SourceElement)
     */
    public boolean equalsModRenaming(Object o, NameAbstractionTable nat) {
        if (!(o instanceof JavaBlock)) {
            return false;
        }
        return equalsModRenaming(((JavaBlock) o).program(), nat);
    }


    /**
     * returns true if the given ProgramElement is equal to the one of the JavaBlock modulo renaming
     * (see comment in SourceElement)
     */
    private boolean equalsModRenaming(JavaProgramElement pe, NameAbstractionTable nat) {
        if (pe == null && program() == null) {
            return true;
        } else if (pe != null && program() != null) {
            return program().equalsModRenaming(pe, nat);
        }
        return false;
    }

    /**
     * returns the java program
     *
     * @return the stored JavaProgramElement
     */
    public JavaProgramElement program() {
        return prg;
    }

    /** toString */
    public String toString() {
        PrettyPrinter printer = PrettyPrinter.purePrinter();
        printer.print(prg);
        return printer.result();
    }

    @Override
    public boolean equalsModProofIrrelevancy(Object obj) {
        if (!(obj instanceof JavaBlock)) {
            return false;
        }
        if (this == obj) {
            return true;
        }
        JavaBlock other = (JavaBlock) obj;
        // quite inefficient, but sufficient
        return toString().equals(other.toString());
    }

    @Override
    public int hashCodeModProofIrrelevancy() {
        if (hashCode == -1) {
            hashCode = toString().hashCode();
            if (hashCode == -1) {
                hashCode = 0;
            }
        }
        return hashCode;
    }
}
