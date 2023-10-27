/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.visitor;

import java.util.Objects;

import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.While;

/**
 * Utilits class used by
 * {@link SymbolicExecutionUtil#containsStatement(MethodFrame, ProgramElement, Services)}.
 *
 * @author Martin Hentschel
 */
public class ContainsStatementVisitor extends JavaASTVisitor {
    /**
     * The {@link ProgramElement} to search.
     */
    private final SourceElement toSearch;

    /**
     * The result.
     */
    private boolean contained = false;

    /**
     * Constructor.
     *
     * @param root The {@link ProgramElement} to start search in.
     * @param toSearch The {@link SourceElement} to search.
     * @param services The {@link Services} to use.
     */
    public ContainsStatementVisitor(ProgramElement root, SourceElement toSearch,
            Services services) {
        super(root, services);
        this.toSearch = toSearch;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected void doDefaultAction(SourceElement se) {
        if (equalsWithPosition(se, toSearch)) {
            // Comparison by == is not possible since loops are recreated
            contained = true;
        }
    }

    /**
     * Returns the result.
     *
     * @return {@code true} contained, {@code false} not contained.
     */
    public boolean isContained() {
        return contained;
    }

    /**
     * Compares the given {@link SourceElement}s including their {@link PositionInfo}s.
     * <p>
     * <strong>NOTE:</strong> (DS) This is a copy of
     * SymbolicExecutionUtil#equalsWithPosition(SourceElement, SourceElement) which has been copied
     * here since it's not possible to create a dependency to its original container project.
     *
     * @param first The first {@link SourceElement}.
     * @param second The second {@link SourceElement}.
     * @return {@code true} both are equal and at the same {@link PositionInfo}, {@code false}
     *         otherwise.
     */
    public static boolean equalsWithPosition(SourceElement first, SourceElement second) {
        if (first != null && second != null) {
            if (first instanceof While) {
                if (second instanceof While) {
                    // Special treatment for while because its position info is
                    // lost during prove, but maintained in its guard.
                    return first.equals(second) && equalsWithPosition(((While) first).getGuard(),
                        ((While) second).getGuard());
                } else {
                    return false;
                }
            } else {
                // Compare all source elements including ints position info
                return first.equals(second)
                        && Objects.equals(first.getPositionInfo(), second.getPositionInfo());
            }
        } else {
            return first == null && second == null;
        }
    }
}
