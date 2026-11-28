/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.ast.pattern;

import java.util.List;
import java.util.Objects;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.JavaNonTerminalProgramElement;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.SourceElement;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.ProgramElementName;

import org.key_project.util.ExtList;

import org.jspecify.annotations.NullMarked;

/**
 * One component pattern of a {@link RecordPattern}.
 *
 * <p>
 * Besides the nested pattern this node carries the name of the record component (which is also the
 * name of the accessor method). The name is resolved from the record declaration during conversion
 * so that later transformations can destructure the record without consulting the Java model
 * again. The accessor name is not printed; it is not part of the source syntax.
 *
 * @author Alexander Weigl
 */
@NullMarked
public class RecordPatternComponent extends JavaNonTerminalProgramElement {

    private final ProgramElementName accessorName;
    private final Pattern pattern;

    public RecordPatternComponent(ProgramElementName accessorName, Pattern pattern) {
        this(PositionInfo.UNDEFINED, List.of(), accessorName, pattern);
    }

    public RecordPatternComponent(ExtList children) {
        super(children);
        this.accessorName = Objects.requireNonNull(children.get(ProgramElementName.class));
        this.pattern = Objects.requireNonNull(children.get(Pattern.class));
    }

    public RecordPatternComponent(PositionInfo pi, List<Comment> comments,
            ProgramElementName accessorName, Pattern pattern) {
        super(pi, comments);
        this.accessorName = Objects.requireNonNull(accessorName);
        this.pattern = Objects.requireNonNull(pattern);
    }

    /**
     * @return the name of the record component (and of its accessor method)
     */
    public ProgramElementName getAccessorName() {
        return accessorName;
    }

    /**
     * @return the pattern matched against the component value
     */
    public Pattern getPattern() {
        return pattern;
    }

    @Override
    public int getChildCount() {
        return 2;
    }

    @Override
    public ProgramElement getChildAt(int index) {
        return switch (index) {
            case 0 -> accessorName;
            case 1 -> pattern;
            default -> throw new IndexOutOfBoundsException(
                "RecordPatternComponent has no child " + index);
        };
    }

    @Override
    public SourceElement getLastElement() {
        return pattern;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnRecordPatternComponent(this);
    }
}
