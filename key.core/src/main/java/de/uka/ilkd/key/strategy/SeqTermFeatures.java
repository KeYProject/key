/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.ldt.BooleanLDT;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.ldt.PSeqLDT;
import de.uka.ilkd.key.ldt.SeqLDT;

import org.key_project.prover.strategy.costbased.termfeature.SubTermFeature;
import org.key_project.prover.strategy.costbased.termfeature.TermFeature;

/// Term features for the sequence theories `Seq` and `PSeq`
public class SeqTermFeatures extends StaticFeatureCollection {

    public final TermFeature get;
    public final TermFeature empty;
    public final TermFeature singleton;
    public final TermFeature concat;
    public final TermFeature subSequence;
    public final TermFeature reverse;
    public final TermFeature upd;
    public final TermFeature def;
    public final TermFeature swap;
    public final TermFeature remove;
    public final TermFeature nPermInv;
    public final TermFeature array2seq;

    /// Checks whether a term is built by a sequence constructor.
    public final TermFeature constructor;
    /// Checks whether a term is a concrete sequence built only from constructors and literals
    public final TermFeature concreteSeq;
    /// Checks whether a term has nested `seqGets` inside a `seqDef`,
    /// e.g., `seqDef{u}(l, h, seqGet(s, u))`
    public final TermFeature defOverGets;

    SeqTermFeatures(SeqLDT seq, PSeqLDT pseq, IntegerLDT ints, BooleanLDT booleans) {
        get = or(opBase(seq.getSeqGet()), opBase(pseq.getPseqGet()));
        empty = or(op(seq.getSeqEmpty()), opBase(pseq.getPseqEmpty()));
        singleton = or(op(seq.getSeqSingleton()), opBase(pseq.getPseqSingleton()));
        concat = or(op(seq.getSeqConcat()), opBase(pseq.getPseqConcat()));
        subSequence = or(op(seq.getSeqSub()), opBase(pseq.getPseqSub()));
        reverse = or(op(seq.getSeqReverse()), opBase(pseq.getPseqReverse()));
        upd = or(op(seq.getSeqUpd()), opBase(pseq.getPseqUpd()));
        def = or(op(seq.getSeqDef()), opBase(pseq.getPseqDef()));
        swap = or(op(seq.getSeqSwap()), opBase(pseq.getPseqSwap()));
        remove = or(op(seq.getSeqRemove()), opBase(pseq.getPseqRemove()));
        nPermInv = or(op(seq.getSeqNPermInv()), op(pseq.getPseqNPermInv()));
        array2seq = op(seq.getArray2seq());

        constructor = or(empty, singleton, concat, subSequence, reverse, upd, def, swap, remove,
            nPermInv, array2seq);
        final TermFeature literal = or(op(ints.getNumberSymbol()), op(ints.getCharSymbol()),
            op(booleans.getTrueConst()), op(booleans.getFalseConst()));
        concreteSeq = add(constructor, rec(not(literal), or(constructor, literal)));
        defOverGets = add(def, SubTermFeature.create(new TermFeature[] { any(), any(), get }));
    }
}
