/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.jml.pretranslation;


import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.speclang.LoopContract;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.njml.LabeledParserRuleContext;

import org.key_project.util.collection.ImmutableList;

import org.antlr.v4.runtime.ParserRuleContext;

/**
 * Objects of this type represent the various JML specification constructs in textual, unprocessed
 * form.
 */
public abstract class TextualJMLConstruct {

    protected final ImmutableList<JMLModifier> modifiers;
    private Location location = new Location(null, Position.UNDEFINED);
    private boolean loopContract;

    /**
     * A user-provided identifier to keep an overview over large specification collections
     */
    protected String name;

    protected TextualJMLConstruct(ImmutableList<JMLModifier> specModifiers) {
        assert specModifiers != null;
        this.modifiers = specModifiers;
    }

    protected TextualJMLConstruct(ImmutableList<JMLModifier> specModifiers, String name) {
        this(specModifiers);
        this.name = name;
    }

    /**
     * @return {@code true} if and only if this is a loop contract.
     * @see LoopContract
     */
    public final boolean isLoopContract() {
        return loopContract;
    }

    /**
     * @param loopContract boolean to identify contract as loop contract
     * @see #isLoopContract()
     */
    public final void setLoopContract(boolean loopContract) {
        this.loopContract = loopContract;
    }

    public final ImmutableList<JMLModifier> getModifiers() {
        return modifiers;
    }

    /**
     * Return the approximate location of this construct. This is usually the position of the
     * specification line parsed first. Implementations can set it using <code>setPosition</code> or
     * <code>addGeneric</code>.
     */
    public Location getLocation() {
        return location;
    }

    /**
     * Sets the approximate position of this construct when first called with a valid position. The
     * approximate position can still be changed while it is undefined. Also set source file name if
     * known.
     *
     * @param ps set position of the construct
     */
    protected void setPosition(PositionedString ps) {
        if (location == null) {
            location = ps.location;
        }
    }

    protected void setPosition(ParserRuleContext ps) {
        location = Location.fromToken(ps.start);
    }

    protected void setPosition(LabeledParserRuleContext ps) {
        setPosition(ps.first);
    }

}
