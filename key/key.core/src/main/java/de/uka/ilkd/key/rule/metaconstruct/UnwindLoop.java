// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.metaconstruct;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * This class is used to perform program transformations needed for the symbolic
 * execution of a loop. It unwinds the loop: e.g. <code>
 * while ( i<10 ) {
 *   i++
 * }
 * </code> becomes if (i<10) l1:{ l2:{ i++; } while (i<10) { i++; } }
 *
 */
public class UnwindLoop extends ProgramTransformer {

    /** the outer label that is used to leave the while loop ('l1') */
    private final SchemaVariable outerLabel;
    /** the inner label ('l2') */
    private final SchemaVariable innerLabel;

    /**
     * creates an unwind-loop ProgramTransformer
     *
     * @param loop
     *            the LoopStatement contained by the meta construct
     * @param innerLabel The inner label SV
     * @param outerLabel The outer label SV
     */
    public UnwindLoop(SchemaVariable innerLabel, SchemaVariable outerLabel,
            LoopStatement loop) {
        super("#unwind-loop", loop);
        this.innerLabel = innerLabel;
        this.outerLabel = outerLabel;
    }

    @Override
    public ProgramElement[] transform(ProgramElement pe, Services services,
            SVInstantiations svInst) {
        if (!(pe instanceof LoopStatement)) {
            return new ProgramElement[] { pe };
        }
        final LoopStatement originalLoop = (LoopStatement) pe;

        final WhileLoopTransformation w = new WhileLoopTransformation(
            originalLoop,
            (ProgramElementName) svInst.getInstantiation(outerLabel),
            (ProgramElementName) svInst.getInstantiation(innerLabel), services);
        w.start();
        return new ProgramElement[] { w.result() };
    }

    @Deprecated
    public SchemaVariable getInnerLabelSV() {
        return innerLabel;
    }

    @Deprecated
    public SchemaVariable getOuterLabelSV() {
        return outerLabel;
    }

    /**
     * return a list of the SV that are relevant to this UnwindLoop
     *
     * @param svInst
     *            the instantiations so far - ignored
     * @return a list of 0 to 2 schema variables (outer/inner label)
     */
    @Override
    public ImmutableList<SchemaVariable> neededInstantiations(
            SVInstantiations svInst) {
        ImmutableList<SchemaVariable> ret = ImmutableSLList
                .<SchemaVariable> nil();

        if (innerLabel != null) {
            ret = ret.prepend(innerLabel);
        }

        if (outerLabel != null) {
            ret = ret.prepend(outerLabel);
        }

        return ret;
    }
}