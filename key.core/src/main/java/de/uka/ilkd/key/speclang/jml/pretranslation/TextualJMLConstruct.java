package de.uka.ilkd.key.speclang.jml.pretranslation;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import javax.annotation.Nonnull;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Name;
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

    protected final ImmutableList<JMLModifier> mods;
    private Position approxPos = Position.UNDEFINED;
    private String sourceFile = null;
    private boolean loopContract;

    /**
     * A user-provided identifier to keep an overview over large specification collections
     */
    protected String name;

    public TextualJMLConstruct(ImmutableList<JMLModifier> mods) {
        assert mods != null;
        this.mods = mods;
    }

    public TextualJMLConstruct(ImmutableList<JMLModifier> mods, String name) {
        this(mods);
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

    public final ImmutableList<JMLModifier> getMods() {
        return mods;
    }

    /**
     * Return the approximate position of this construct. This is usually the position of the
     * specification line parsed first. Implementations can set it using <code>setPosition</code> or
     * <code>addGeneric</code>.
     */
    public Position getApproxPosition() {
        return approxPos;
    }

    /**
     * Return the source file name where this construct appears.
     */
    public String getSourceFileName() {
        return sourceFile;
    }

    /**
     * Sets the approximate position of this construct when first called with a valid position. The
     * approximate position can still be changed while it is undefined. Also set source file name if
     * known.
     *
     * @param ps set position of the construct
     */
    protected void setPosition(PositionedString ps) {
        if (sourceFile == null) {
            approxPos = ps.pos;
            sourceFile = ps.fileName;
        }
    }

    protected void setPosition(ParserRuleContext ps) {
        sourceFile = ps.start.getTokenSource().getSourceName();
        approxPos = Position.fromToken(ps.start);
    }

    protected void setPosition(LabeledParserRuleContext ps) {
        setPosition(ps.first);
    }

    /**
     * @param item
     * @param ps
     * @deprecated
     */
    @Deprecated
    protected void addGeneric(Map<String, ImmutableList<LabeledParserRuleContext>> item,
            @Nonnull LabeledParserRuleContext ps) {
        String t = ps.first.getText();
        if (!t.startsWith("<") || t.startsWith("<inv>")) {
            ImmutableList<LabeledParserRuleContext> l = item.get(HeapLDT.BASE_HEAP_NAME.toString());
            l = l.append(ps);
            item.put(HeapLDT.BASE_HEAP_NAME.toString(), l);
            return;
        }
        List<String> hs = new ArrayList<>();
        while (t.startsWith("<") && !t.startsWith("<inv>")) {
            for (Name heapName : HeapLDT.VALID_HEAP_NAMES) {
                for (String hName : new String[] { heapName.toString(),
                    heapName + "AtPre" }) {
                    String h = "<" + hName + ">";
                    if (t.startsWith(h)) {
                        hs.add(hName);
                        t = t.substring(h.length());
                    }
                }
            }
        }
        /*
         * if (ps.hasLabels()) { ps = new PositionedString(t, ps.fileName,
         * ps.pos).label(ps.getLabels()); } else {
         */

        // ps = new PositionedString(t, ps.fileName, ps.pos);

        for (String h : hs) {
            ImmutableList<LabeledParserRuleContext> l = item.get(h);
            l = l.append(ps);
            item.put(h, l);
        }
        setPosition(ps);
    }

}
